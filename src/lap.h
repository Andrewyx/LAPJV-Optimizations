/*
 *   Copyright (c) 2007 John Weaver
 *   Copyright (c) 2015 Miroslav Krajicek
 *
 *   This program is free software; you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation; either version 2 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program; if not, write to the Free Software
 *   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
 */

#if !defined(_LAPJV_H_)
#define _LAPJV_H_

#include "matrix.h"
#include <algorithm> // Needed for std::max
#include <cmath>     // Needed for std::abs
#include <vector>

/*************** TYPES      *******************/

typedef int row;
typedef int col;
typedef double cost;

template <typename Data>
class LAPJV
{
public:
    static constexpr double EPSILON = 1e-9;
    static constexpr double BIG = 1.79769e+308;

    void solve(Matrix<Data>& m)
    {
        // INITIALIZATION
        int original_rows = m.rows();
        int original_cols = m.columns();
        // LAPJV requires a square matrix. Pad to the largest dimension.
        int dim = std::max(original_rows, original_cols);

        // Helper lambda to seamlessly provide 0-cost padding for out-of-bounds access
        auto cost_at = [&](int r, int c) -> Data {
            // 0 cost ensures "dummy" assignments don't penalize the real assignments
            return r < original_rows && c < original_cols ? m(r, c) : 0;
        };

        // row_assignment[i] = column assigned to row i
        std::vector<col> row_assignment(dim, 0);
        // col_assignment[j] = row assigned to column j, or -1 if unassigned
        std::vector<row> col_assignment(dim, 0);
        
        // Dual variables for rows (u) and columns (v)
        std::vector<cost> dual_u(dim, 0);
        std::vector<cost> dual_v(dim, 0);

        std::vector<row> unassigned_rows(dim, 0);
        
        // Structures used for shortest path calculations (Dijkstra)
        std::vector<col> path_cols(dim, 0);
        std::vector<col> col_match_counts(dim, 0);
        std::vector<cost> shortest_path_costs(dim, 0);
        std::vector<row> predecessor_rows(dim, 0);

        auto column_reduction = [&]() -> cost {
            std::vector<row> min_rows(dim, 0);

            // STEP 1: COLUMN REDUCTION
            // Initialize with the first row's costs
            for (col j = 0; j < dim; j++)
            {
                dual_v[j] = cost_at(0, j);
            }

            // Row-major access for cache-friendly matrix reads
            for (row i = 1; i < dim; i++)
            {
                #pragma omp simd
                for (col j = 0; j < dim; j++)
                {
                    cost c = cost_at(i, j);
                    if (c < dual_v[j])
                    {
                        dual_v[j] = c;
                        min_rows[j] = i;
                    }
                }
            }

            cost current_min_cost = 0;

            // Assign columns backwards to match original LAPJV behavior
            for (col j = dim; j--;)
            {
                row min_row = min_rows[j];
                current_min_cost = dual_v[j];

                // Track the number of times a row contains the minimum of a column
                if (++col_match_counts[min_row] == 1)
                {
                    // First time we see this row as a minimum, tentatively assign it
                    row_assignment[min_row] = j;
                    col_assignment[j] = min_row;
                }
                else if (dual_v[j] < dual_v[row_assignment[min_row]])
                {
                    // If the row was already assigned, but this column has a lower minimum cost,
                    // reassign the row to this new column.
                    int prev_j = row_assignment[min_row];
                    row_assignment[min_row] = j;
                    col_assignment[j] = min_row;
                    col_assignment[prev_j] = -1;
                }
                else
                {
                    // Otherwise, this column remains unassigned for now.
                    col_assignment[j] = -1;
                }
            }
            return current_min_cost;
        };

        cost min_reduced_cost = column_reduction();
        row num_unassigned_rows = 0;
        
        // STEP 2: REDUCTION TRANSFER
        // Transfer the reduction from rows that have exactly one assigned column.
        for (row i = 0; i < dim; i++)
        {
            if (col_match_counts[i] == 0)
            {
                // Row has no assignments
                unassigned_rows[num_unassigned_rows++] = i;
            }
            else if (col_match_counts[i] == 1)
            {
                // Row is uniquely assigned to a column
                col j1 = row_assignment[i];
                min_reduced_cost = BIG;
                for (col j = 0; j < dim; j++)
                {
                    if (j != j1)
                    {
                        if (cost_at(i, j) - dual_v[j] < min_reduced_cost)
                        {
                            min_reduced_cost = cost_at(i, j) - dual_v[j];
                        }
                    }
                }
                dual_v[j1] = dual_v[j1] - min_reduced_cost;
            }
        }

        // STEP 3: AUGMENTING ROW REDUCTION
        // Further reduce costs by examining unassigned rows.
        int loopcnt = 0;
        do
        {
            loopcnt++;

            row k = 0;
            row prev_num_unassigned = num_unassigned_rows;
            num_unassigned_rows = 0;
            while (k < prev_num_unassigned)
            {
                row i = unassigned_rows[k];
                k++;

                // Find the two smallest reduced costs in row i
                cost min_cost = cost_at(i, 0) - dual_v[0];
                col best_col = 0;
                cost second_min_cost = BIG;
                col second_best_col = 0;
                
                for (col j = 1; j < dim; j++)
                {
                    cost reduced_cost = cost_at(i, j) - dual_v[j];
                    if (reduced_cost < second_min_cost)
                    {
                        if (reduced_cost >= min_cost)
                        {
                            second_min_cost = reduced_cost;
                            second_best_col = j;
                        }
                        else
                        {
                            second_min_cost = min_cost;
                            min_cost = reduced_cost;
                            second_best_col = best_col;
                            best_col = j;
                        }
                    }
                }

                row previously_assigned_row = col_assignment[best_col];
                if (second_min_cost - min_cost > EPSILON)
                {
                    dual_v[best_col] = dual_v[best_col] - (second_min_cost - min_cost);
                }
                else if (previously_assigned_row > -1)
                {
                    best_col = second_best_col;
                    previously_assigned_row = col_assignment[second_best_col];
                }

                // Assign row i to the best column found
                row_assignment[i] = best_col;
                col_assignment[best_col] = i;

                if (previously_assigned_row > -1)
                {
                    // The column was already assigned to another row.
                    // We displaced it, so add the displaced row back to the unassigned list.
                    if (second_min_cost - min_cost > EPSILON)
                    {
                        unassigned_rows[--k] = previously_assigned_row;
                    }
                    else
                    {
                        unassigned_rows[num_unassigned_rows++] = previously_assigned_row;
                    }
                }
            }
        }
        while (loopcnt < 2);

        // STEP 4: AUGMENT SOLUTION
        // For each remaining unassigned row, find an augmenting path to increase assignments.
        // This is effectively Dijkstra's algorithm for finding the shortest alternating path.
        for (row f = 0; f < num_unassigned_rows; f++)
        {
            row current_free_row = unassigned_rows[f];

            // Initialize shortest path costs
            for (col j = 0; j < dim; j++)
            {
                shortest_path_costs[j] = cost_at(current_free_row, j) - dual_v[j];
                predecessor_rows[j] = current_free_row;
                path_cols[j] = j;
            }

            col search_head = 0;
            col search_tail = 0;
            bool unassigned_found = false;
            col end_of_path = 0;
            col last_processed = 0;

            do
            {
                if (search_tail == search_head)
                {
                    last_processed = search_head - 1;

                    min_reduced_cost = shortest_path_costs[path_cols[search_tail++]];
                    for (col k = search_tail; k < dim; k++)
                    {
                        col j = path_cols[k];
                        cost current_cost = shortest_path_costs[j];
                        if (current_cost <= min_reduced_cost + EPSILON)
                        {
                            if (current_cost < min_reduced_cost - EPSILON)
                            {
                                search_tail = search_head;
                                min_reduced_cost = current_cost;
                            }
                            path_cols[k] = path_cols[search_tail];
                            path_cols[search_tail++] = j;
                        }
                    }
                    for (col k = search_head; k < search_tail; k++)
                    {
                        if (col_assignment[path_cols[k]] < 0)
                        {
                            end_of_path = path_cols[k];
                            unassigned_found = true;
                            break;
                        }
                    }
                }

                if (!unassigned_found)
                {
                    col next_col_to_process = path_cols[search_head];
                    search_head++;
                    row assigned_row = col_assignment[next_col_to_process];
                    cost current_cost_margin = cost_at(assigned_row, next_col_to_process) - dual_v[next_col_to_process] - min_reduced_cost;

                    for (col k = search_tail; k < dim; k++)
                    {
                        col j = path_cols[k];
                        cost new_cost = cost_at(assigned_row, j) - dual_v[j] - current_cost_margin;
                        if (new_cost < shortest_path_costs[j])
                        {
                            predecessor_rows[j] = assigned_row;
                            if (std::abs(new_cost - min_reduced_cost) <= EPSILON)
                            {
                                if (col_assignment[j] < 0)
                                {
                                    end_of_path = j;
                                    unassigned_found = true;
                                    break;
                                }
                                else
                                {
                                    path_cols[k] = path_cols[search_tail];
                                    path_cols[search_tail++] = j;
                                }
                            }
                            shortest_path_costs[j] = new_cost;
                        }
                    }
                }
            }
            while (!unassigned_found);

            // Update dual variables along the alternating path
            for (col k = last_processed + 1; k--;)
            {
                col j1 = path_cols[k];
                dual_v[j1] = dual_v[j1] + shortest_path_costs[j1] - min_reduced_cost;
            }

            // Augment the current matching
            row i;
            col j1;
            do
            {
                i = predecessor_rows[end_of_path];
                col_assignment[end_of_path] = i;
                j1 = end_of_path;
                end_of_path = row_assignment[i];
                row_assignment[i] = j1;
            }
            while (i != current_free_row);
        }

        // STEP 5: CALCULATE OPTIMAL COST & FINALIZE
        cost lapcost = 0;
        for (row i = 0; i < dim; i++)
        {
            col j = row_assignment[i];
            dual_u[i] = cost_at(i, j) - dual_v[j];
            lapcost = lapcost + cost_at(i, j);
        }

        // Write assignments back into the input matrix
        for (size_t r = 0; r < m.rows(); ++r)
        {
            for (size_t c = 0; c < m.columns(); ++c)
            {
                if (row_assignment[r] == (col)c)
                {
                    m(r, c) = 0.0;
                }
                else
                {
                    m(r, c) = -1.0;
                }
            }
        }
    }

private:
};

#endif /* !defined(_LAPJV_H_) */