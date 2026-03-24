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
// #define DEBUG

#include "matrix.h"
#include <algorithm>
#include <cmath>
#include <vector>

/*************** TYPES      *******************/

typedef int row;
typedef int col;

template <typename Data>
class LAPJV
{
public:
    static constexpr Data EPSILON = std::is_integral_v<Data>
                                        ? static_cast<Data>(0)
                                        : std::numeric_limits<Data>::epsilon() * static_cast<Data>(100);
    static constexpr Data BIG = std::numeric_limits<Data>::max();
    typedef Data cost;

    void solve(Matrix<Data>& m)
    {
        int original_rows = m.rows();
        int original_cols = m.columns();
        int dim = std::max(original_rows, original_cols);

        Context ctx(dim, original_rows, original_cols, m.data());

        step1_column_reduction(m, ctx);
        step2_reduction_transfer(m, ctx);
        step3_augmenting_row_reduction(m, ctx);
        step4_augment_solution(m, ctx);
        step5_calculate_optimal_cost_and_finalize(m, ctx);
    }

private:
    struct Context
    {
        int dim;
        int original_rows;
        int original_cols;
        const Data* __restrict__ m_data;
        std::vector<col> row_assignment;
        std::vector<row> col_assignment;
        std::vector<cost> dual_u;
        std::vector<cost> dual_v;
        std::vector<row> unassigned_rows;
        std::vector<col> path_cols;
        std::vector<col> col_match_counts;
        std::vector<cost> shortest_path_costs;
        std::vector<row> predecessor_rows;
        cost min_reduced_cost;
        row num_unassigned_rows;

        explicit Context(int d, int r, int c, const Data* data_ptr)
            : dim(d), original_rows(r), original_cols(c), m_data(data_ptr),
              row_assignment(d, 0), col_assignment(d, 0),
              dual_u(d, 0), dual_v(d, 0),
              unassigned_rows(d, 0), path_cols(d, 0),
              col_match_counts(d, 0), shortest_path_costs(d, 0),
              predecessor_rows(d, 0),
              min_reduced_cost(0), num_unassigned_rows(0)
        {
        }
    };

    static cost cost_at(const Matrix<Data>& m, const Context& ctx, int r, int c)
    {
        if (r < ctx.original_rows && c < ctx.original_cols) [[likely]] {
            return ctx.m_data[r * ctx.original_cols + c];
        }
        return 0;
    }

#ifdef DEBUG
    __attribute__((noinline))
#endif
    void step1_column_reduction(const Matrix<Data>& m, Context& ctx)
    {
        // row with the min given a column
        std::vector<row> min_rows(ctx.dim, 0);

        // find mins for columns
#pragma omp simd
        for (col j = 0; j < ctx.dim; j++)
        {
            ctx.dual_v[j] = cost_at(m, ctx, 0, j);
        }

        for (row i = 1; i < ctx.dim; i++)
        {
#pragma omp simd
            for (col j = 0; j < ctx.dim; j++)
            {
                cost c = cost_at(m, ctx, i, j);
                if (c < ctx.dual_v[j])
                {
                    ctx.dual_v[j] = c;
                    min_rows[j] = i;
                }
            }
        }
        step1_2_partial_assignment(ctx, min_rows);
    }


#ifdef DEBUG
    __attribute__((noinline))
#endif
    void step1_2_partial_assignment(Context& ctx, const std::vector<row>& min_rows)
    {
        cost current_min_cost = 0;
        for (col j = ctx.dim; j--;)
        {
            row min_row = min_rows[j];
            current_min_cost = ctx.dual_v[j];

            // increment and assign
            if (++ctx.col_match_counts[min_row] == 1)
            {
                ctx.row_assignment[min_row] = j;
                ctx.col_assignment[j] = min_row;
            }
            else if (ctx.dual_v[j] < ctx.dual_v[ctx.row_assignment[min_row]])
            {
                // replace if cheaper
                int prev_j = ctx.row_assignment[min_row];
                ctx.row_assignment[min_row] = j;
                ctx.col_assignment[j] = min_row;
                ctx.col_assignment[prev_j] = -1;
            }
            else
            {
                // worse option, leave unassigned
                ctx.col_assignment[j] = -1;
            }
        }
        ctx.min_reduced_cost = current_min_cost;
    }

#ifdef DEBUG
    __attribute__((noinline))
#endif
    void step2_reduction_transfer(const Matrix<Data>& m, Context& ctx)
    {
        // count assignments and increase their margin of selection
        ctx.num_unassigned_rows = 0;
        for (row i = 0; i < ctx.dim; i++)
        {
            if (ctx.col_match_counts[i] == 0)
            {
                ctx.unassigned_rows[ctx.num_unassigned_rows++] = i;
            }
            else if (ctx.col_match_counts[i] == 1)
            {
                col j1 = ctx.row_assignment[i];
                ctx.min_reduced_cost = BIG;
                for (col j = 0; j < ctx.dim; j++)
                {
                    if (j != j1 && cost_at(m, ctx, i, j) - ctx.dual_v[j] < ctx.min_reduced_cost)
                    {
                        ctx.min_reduced_cost = cost_at(m, ctx, i, j) - ctx.dual_v[j];
                    }
                }
                // reduce the price by the diff w the 2nd cheapest to make it harder to change
                ctx.dual_v[j1] -= ctx.min_reduced_cost;
            }
        }
    }

#ifdef DEBUG
    __attribute__((noinline))
#endif
    void step3_augmenting_row_reduction(const Matrix<Data>& m, Context& ctx)
    {
        int loopcnt = 0;
        do
        {
            loopcnt++;
            row k = 0;
            row prev_num_unassigned = ctx.num_unassigned_rows;
            ctx.num_unassigned_rows = 0;
            while (k < prev_num_unassigned)
            {
                row i = ctx.unassigned_rows[k];
                k++;

                cost min_cost = cost_at(m, ctx, i, 0) - ctx.dual_v[0];
                col best_col = 0;
                cost second_min_cost = BIG;
                col second_best_col = 0;

                for (col j = 1; j < ctx.dim; j++)
                {
                    cost reduced_cost = cost_at(m, ctx, i, j) - ctx.dual_v[j];
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

                row previously_assigned_row = ctx.col_assignment[best_col];
                if (second_min_cost - min_cost > EPSILON)
                {
                    ctx.dual_v[best_col] = ctx.dual_v[best_col] - (second_min_cost - min_cost);
                }
                else if (previously_assigned_row > -1)
                {
                    best_col = second_best_col;
                    previously_assigned_row = ctx.col_assignment[second_best_col];
                }

                ctx.row_assignment[i] = best_col;
                ctx.col_assignment[best_col] = i;

                if (previously_assigned_row > -1)
                {
                    if (second_min_cost - min_cost > EPSILON)
                    {
                        ctx.unassigned_rows[--k] = previously_assigned_row;
                    }
                    else
                    {
                        ctx.unassigned_rows[ctx.num_unassigned_rows++] = previously_assigned_row;
                    }
                }
            }
        }
        while (loopcnt < 2);
    }

#ifdef DEBUG
    __attribute__((noinline))
#endif
    void step4_augment_solution(const Matrix<Data>& m, Context& ctx)
    {
        for (row f = 0; f < ctx.num_unassigned_rows; f++)
        {
            row current_free_row = ctx.unassigned_rows[f];

            for (col j = 0; j < ctx.dim; j++)
            {
                ctx.shortest_path_costs[j] = cost_at(m, ctx, current_free_row, j) - ctx.dual_v[j];
                ctx.predecessor_rows[j] = current_free_row;
                ctx.path_cols[j] = j;
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

                    ctx.min_reduced_cost = ctx.shortest_path_costs[ctx.path_cols[search_tail++]];
                    for (col k = search_tail; k < ctx.dim; k++)
                    {
                        col j = ctx.path_cols[k];
                        cost current_cost = ctx.shortest_path_costs[j];
                        if (current_cost <= ctx.min_reduced_cost + EPSILON)
                        {
                            if (current_cost < ctx.min_reduced_cost - EPSILON)
                            {
                                search_tail = search_head;
                                ctx.min_reduced_cost = current_cost;
                            }
                            ctx.path_cols[k] = ctx.path_cols[search_tail];
                            ctx.path_cols[search_tail++] = j;
                        }
                    }
                    for (col k = search_head; k < search_tail; k++)
                    {
                        if (ctx.col_assignment[ctx.path_cols[k]] < 0)
                        {
                            end_of_path = ctx.path_cols[k];
                            unassigned_found = true;
                            break;
                        }
                    }
                }

                if (!unassigned_found)
                {
                    col next_col_to_process = ctx.path_cols[search_head];
                    search_head++;
                    row assigned_row = ctx.col_assignment[next_col_to_process];
                    cost current_cost_margin = cost_at(m, ctx, assigned_row, next_col_to_process) - ctx.dual_v[
                        next_col_to_process] - ctx.min_reduced_cost;

                    for (col k = search_tail; k < ctx.dim; k++)
                    {
                        col j = ctx.path_cols[k];
                        cost new_cost = cost_at(m, ctx, assigned_row, j) - ctx.dual_v[j] - current_cost_margin;
                        if (new_cost < ctx.shortest_path_costs[j])
                        {
                            ctx.predecessor_rows[j] = assigned_row;
                            if (std::abs(new_cost - ctx.min_reduced_cost) <= EPSILON)
                            {
                                if (ctx.col_assignment[j] < 0)
                                {
                                    end_of_path = j;
                                    unassigned_found = true;
                                    break;
                                }
                                else
                                {
                                    ctx.path_cols[k] = ctx.path_cols[search_tail];
                                    ctx.path_cols[search_tail++] = j;
                                }
                            }
                            ctx.shortest_path_costs[j] = new_cost;
                        }
                    }
                }
            }
            while (!unassigned_found);

            for (col k = last_processed + 1; k--;)
            {
                col j1 = ctx.path_cols[k];
                ctx.dual_v[j1] = ctx.dual_v[j1] + ctx.shortest_path_costs[j1] - ctx.min_reduced_cost;
            }

            row i;
            col j1;
            do
            {
                i = ctx.predecessor_rows[end_of_path];
                ctx.col_assignment[end_of_path] = i;
                j1 = end_of_path;
                end_of_path = ctx.row_assignment[i];
                ctx.row_assignment[i] = j1;
            }
            while (i != current_free_row);
        }
    }

#ifdef DEBUG
    __attribute__((noinline))
#endif
    void step5_calculate_optimal_cost_and_finalize(Matrix<Data>& m, Context& ctx)
    {
        cost lapcost = 0;
        for (row i = 0; i < ctx.dim; i++)
        {
            col j = ctx.row_assignment[i];
            ctx.dual_u[i] = cost_at(m, ctx, i, j) - ctx.dual_v[j];
            lapcost = lapcost + cost_at(m, ctx, i, j);
        }

        for (size_t r = 0; r < m.rows(); ++r)
        {
            for (size_t c = 0; c < m.columns(); ++c)
            {
                if (ctx.row_assignment[r] == static_cast<col>(c))
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
};

#endif /* !defined(_LAPJV_H_) */
