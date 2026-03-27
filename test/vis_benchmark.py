import json
import sys
import re
from datetime import datetime
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.backends.backend_pdf import PdfPages
import os

def parse_benchmark_data(json_path):
    with open(json_path, 'r') as f:
        data = json.load(f)

    context = data.get("context", {})
    benchmarks = data.get("benchmarks", [])

    # Storage for our parsed data
    series = {
        'double': {'n': [], 'time': [], 'iterations': []},
        'float': {'n': [], 'time': [], 'iterations': []},
        'int': {'n': [], 'time': [], 'iterations': []}
    }
    big_o_stats = {}

    for b in benchmarks:
        name = b.get("name", "")

        # Extract the type (double, float, int) from the template signature
        type_match = re.search(r'<([a-z]+)>', name)
        if not type_match:
            continue
        dtype = type_match.group(1)

        # Handle Big-O and RMS summary rows
        if "_BigO" in name:
            big_o_stats[dtype] = b.get("big_o", "Unknown")
            continue
        if "_RMS" in name:
            continue

        # Extract the matrix size (N)
        size_match = re.search(r'/(\d+)', name)
        if size_match and "cpu_time" in b:
            n = int(size_match.group(1))
            series[dtype]['n'].append(n)
            series[dtype]['time'].append(b["cpu_time"])
            series[dtype]['iterations'].append(b.get("iterations", 0))

    return context, series, big_o_stats

def plot_to_pdf(context, series, big_o_stats, output_pdf):
    with PdfPages(output_pdf) as pdf:
        # --- PAGE 1: System Context & Metadata ---
        # (Same as before)
        fig_context = plt.figure(figsize=(8, 6))
        plt.axis('off')
        date_str = context.get("date", "Unknown Date")
        context_text = (
            f"LAPJV Benchmark Execution Report\n"
            f"{'='*40}\n\n"
            f"Date: {date_str}\n"
            f"Host: {context.get('host_name', 'Unknown')}\n\n"
            f"CPU Info:\n"
            f"  - Cores: {context.get('num_cpus', 'Unknown')}\n"
            f"  - Clock Speed: {context.get('mhz_per_cpu', 'Unknown')} MHz\n\n"
            f"Calculated Complexity:\n"
        )
        for dtype, stat in big_o_stats.items():
            context_text += f"  - {dtype}: O({stat})\n"
        plt.text(0.05, 0.95, context_text, fontsize=10, family='monospace', va='top')
        pdf.savefig(fig_context)
        plt.close()

        # --- PAGE 2: Linear Plot ---
        # (Same as before)
        fig_linear, ax1 = plt.subplots(figsize=(10, 6))
        colors = {'double': '#1f77b4', 'float': '#2ca02c', 'int': '#d62728'}
        for dtype, data in series.items():
            if data['n']:
                ax1.plot(data['n'], data['time'], 'o-', color=colors[dtype], label=dtype)
        ax1.set_title("Execution Time (Linear)")
        ax1.legend()
        ax1.grid(True, ls='--')
        pdf.savefig(fig_linear)
        plt.close()

        # --- PAGE 3: Log-Log Plot ---
        # (Same as before)
        fig_log, ax2 = plt.subplots(figsize=(10, 6))
        for dtype, data in series.items():
            if data['n']:
                ax2.plot(data['n'], data['time'], 'o-', color=colors[dtype], label=dtype)
        ax2.set_xscale('log', base=2)
        ax2.set_yscale('log', base=10)
        ax2.set_title("Execution Time (Log-Log)")
        ax2.grid(True, which="both", ls="--")
        pdf.savefig(fig_log)
        plt.close()

        # --- PAGE 4: Comparative Bar Charts ---
        # We find all unique N values and plot a bar for each type
        all_n = sorted(list(set(n for d in series.values() for n in d['n'])))

        # Dynamically calculate rows needed for 2 columns
        cols = 2
        rows = (len(all_n) + 1) // 2

        # Scale the figure height dynamically based on the number of rows
        fig_bar, axes = plt.subplots(rows, cols, figsize=(12, 4 * rows))
        axes = axes.flatten()

        for idx, n_val in enumerate(all_n):
            ax = axes[idx]
            labels = []
            times = []
            bar_colors = []

            for dtype in ['int', 'float', 'double']:
                if n_val in series[dtype]['n']:
                    n_idx = series[dtype]['n'].index(n_val)
                    labels.append(dtype)
                    times.append(series[dtype]['time'][n_idx])
                    bar_colors.append(colors[dtype])

            bars = ax.bar(labels, times, color=bar_colors, alpha=0.8)
            ax.set_title(f"Matrix Size: {n_val}x{n_val}")
            ax.set_ylabel("CPU Time (ns)")

            # Add text labels on top of bars
            for bar in bars:
                height = bar.get_height()
                ax.text(bar.get_x() + bar.get_width()/2., height,
                        f'{int(height):,}', ha='center', va='bottom', fontsize=9)

        # Hide any unused subplots (e.g., if we have an odd number of charts like 7)
        for idx in range(len(all_n), len(axes)):
            fig_bar.delaxes(axes[idx])

        plt.tight_layout(rect=[0, 0.03, 1, 0.97])
        fig_bar.suptitle("Detailed Type Comparison per Dimension", fontsize=16)
        pdf.savefig(fig_bar)
        plt.close()

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 visualize_benchmarks.py <path_to_results.json>")
        sys.exit(1)

    input_file = sys.argv[1]

    workspace_dir = os.environ.get("BUILD_WORKSPACE_DIRECTORY", ".")

    report_dir = os.path.join(workspace_dir, "reports")
    os.makedirs(report_dir, exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M")

    output_filename = os.path.join(report_dir, f"LAPJV_Benchmark_Report_{timestamp}.pdf")

    context, series, big_o_stats = parse_benchmark_data(input_file)
    plot_to_pdf(context, series, big_o_stats, output_filename)