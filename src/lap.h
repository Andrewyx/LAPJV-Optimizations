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

/*************** TYPES      *******************/

typedef int row;
typedef int col;
typedef double cost;

struct MatrixPosition
{
    row i;
    col j;
};


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

        bool unassignedfound;

        row numfree = 0, prvnumfree, f, i0, k, freerow, *pred, *freeunassigned;
        col j1, j2, endofpath, last, low, up, *collist, *matches;
        cost min, h, umin, usubmin, v2, *d;

        col* row_solutions = new col[dim];
        row* col_solutions = new row[dim];
        cost* u = new cost[dim];
        cost* v = new cost[dim];

        freeunassigned = new row[dim];
        collist = new col[dim];
        matches = new col[dim];
        d = new cost[dim];
        pred = new row[dim];

        MatrixPosition pos_;
        for (pos_.i = 0; pos_.i < dim; pos_.i++) matches[pos_.i] = 0;

        auto column_reduction = [&]() -> cost {
            row imin = 0;
            cost min = 0;
            // COLUMN REDUCTION
            for (pos_.j = dim; pos_.j--;)
            {
                min = cost_at(0, pos_.j);
                imin = 0;
                for (pos_.i = 1; pos_.i < dim; pos_.i++)
                {
                    if (cost_at(pos_.i, pos_.j) < min)
                    {
                        min = cost_at(pos_.i, pos_.j);
                        imin = pos_.i;
                    }
                }
                v[pos_.j] = min;

                if (++matches[imin] == 1)
                {
                    row_solutions[imin] = pos_.j;
                    col_solutions[pos_.j] = imin;
                }
                else if (v[pos_.j] < v[row_solutions[imin]])
                {
                    int j1 = row_solutions[imin];
                    row_solutions[imin] = pos_.j;
                    col_solutions[pos_.j] = imin;
                    col_solutions[j1] = -1;
                }
                else
                {
                    col_solutions[pos_.j] = -1;
                }
            }
            return min;
        };


        min = column_reduction();
        // REDUCTION TRANSFER
        for (pos_.i = 0; pos_.i < dim; pos_.i++)
        {
            if (matches[pos_.i] == 0)
                freeunassigned[numfree++] = pos_.i;
            else if (matches[pos_.i] == 1)
            {
                j1 = row_solutions[pos_.i];
                min = BIG;
                for (pos_.j = 0; pos_.j < dim; pos_.j++)
                    if (pos_.j != j1)
                        if (cost_at(pos_.i, pos_.j) - v[pos_.j] < min) min = cost_at(pos_.i, pos_.j) - v[pos_.j];
                v[j1] = v[j1] - min;
            }
        }

        // AUGMENTING ROW REDUCTION
        int loopcnt = 0;
        do
        {
            loopcnt++;

            k = 0;
            prvnumfree = numfree;
            numfree = 0;
            while (k < prvnumfree)
            {
                pos_.i = freeunassigned[k];
                k++;

                umin = cost_at(pos_.i, 0) - v[0];
                j1 = 0;
                usubmin = BIG;
                for (pos_.j = 1; pos_.j < dim; pos_.j++)
                {
                    h = cost_at(pos_.i, pos_.j) - v[pos_.j];
                    if (h < usubmin)
                        if (h >= umin)
                        {
                            usubmin = h;
                            j2 = pos_.j;
                        }
                        else
                        {
                            usubmin = umin;
                            umin = h;
                            j2 = j1;
                            j1 = pos_.j;
                        }
                }

                i0 = col_solutions[j1];
                if (usubmin - umin > EPSILON)
                    v[j1] = v[j1] - (usubmin - umin);
                else if (i0 > -1)
                {
                    j1 = j2;
                    i0 = col_solutions[j2];
                }

                row_solutions[pos_.i] = j1;
                col_solutions[j1] = pos_.i;

                if (i0 > -1)
                    if (usubmin - umin > EPSILON)
                        freeunassigned[--k] = i0;
                    else
                        freeunassigned[numfree++] = i0;
            }
        }
        while (loopcnt < 2);

        // AUGMENT SOLUTION for each free row.
        for (f = 0; f < numfree; f++)
        {
            freerow = freeunassigned[f];

            for (pos_.j = dim; pos_.j--;)
            {
                d[pos_.j] = cost_at(freerow, pos_.j) - v[pos_.j];
                pred[pos_.j] = freerow;
                collist[pos_.j] = pos_.j;
            }

            low = 0;
            up = 0;
            unassignedfound = false;
            do
            {
                if (up == low)
                {
                    last = low - 1;

                    min = d[collist[up++]];
                    for (k = up; k < dim; k++)
                    {
                        pos_.j = collist[k];
                        h = d[pos_.j];
                        if (h <= min + EPSILON)
                        {
                            if (h < min - EPSILON)
                            {
                                up = low;
                                min = h;
                            }
                            collist[k] = collist[up];
                            collist[up++] = pos_.j;
                        }
                    }
                    for (k = low; k < up; k++)
                        if (col_solutions[collist[k]] < 0)
                        {
                            endofpath = collist[k];
                            unassignedfound = true;
                            break;
                        }
                }

                if (!unassignedfound)
                {
                    j1 = collist[low];
                    low++;
                    pos_.i = col_solutions[j1];
                    h = cost_at(pos_.i, j1) - v[j1] - min;

                    for (k = up; k < dim; k++)
                    {
                        pos_.j = collist[k];
                        v2 = cost_at(pos_.i, pos_.j) - v[pos_.j] - h;
                        if (v2 < d[pos_.j])
                        {
                            pred[pos_.j] = pos_.i;
                            if (std::abs(v2 - min) <= EPSILON)
                                if (col_solutions[pos_.j] < 0)
                                {
                                    endofpath = pos_.j;
                                    unassignedfound = true;
                                    break;
                                }
                                else
                                {
                                    collist[k] = collist[up];
                                    collist[up++] = pos_.j;
                                }
                            d[pos_.j] = v2;
                        }
                    }
                }
            }
            while (!unassignedfound);

            for (k = last + 1; k--;)
            {
                j1 = collist[k];
                v[j1] = v[j1] + d[j1] - min;
            }

            do
            {
                pos_.i = pred[endofpath];
                col_solutions[endofpath] = pos_.i;
                j1 = endofpath;
                endofpath = row_solutions[pos_.i];
                row_solutions[pos_.i] = j1;
            }
            while (pos_.i != freerow);
        }

        // calculate optimal cost.
        cost lapcost = 0;
        for (pos_.i = dim; pos_.i--;)
        {
            pos_.j = row_solutions[pos_.i];
            u[pos_.i] = cost_at(pos_.i, pos_.j) - v[pos_.j];
            lapcost = lapcost + cost_at(pos_.i, pos_.j);
        }

        // Write assignments back into the input matrix
        for (size_t r = 0; r < m.rows(); ++r)
        {
            for (size_t c = 0; c < m.columns(); ++c)
            {
                if (row_solutions[r] == (col)c)
                {
                    m(r, c) = 0.0;
                }
                else
                {
                    m(r, c) = -1.0;
                }
            }
        }

        // free reserved memory.
        delete[] pred;
        delete[] freeunassigned;
        delete[] collist;
        delete[] matches;
        delete[] d;

        delete[] row_solutions;
        delete[] col_solutions;
        delete[] u;
        delete[] v;
    };

private:
};

#endif /* !defined(_LAPJV_H_) */
