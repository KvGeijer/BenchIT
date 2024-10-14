import argparse
import subprocess
import re
import os
from dataclasses import dataclass
import pandas as pd
import seaborn as sns
import matplotlib.pyplot as plt
from io import StringIO  # Import StringIO from io


KERNEL_PATH = "./kernel/arch_x86-64/memory_latency/C/pthread/0/read"
BINARY_PATH = "./bin/arch_x86-64.memory_latency.C.pthread.0.read.0"
BASE_PARAMETERS_PATH = "kernel/arch_x86-64/memory_latency/C/pthread/0/read/PARAMETERS_ATHENA_1LEVELS"
COMPILE_CMD = "./COMPILE.SH"
RUN_CMD = "./RUN.SH"


@dataclass
class Config:
    test_name: str
    cache_state: str = "E"


def parse_arguments() -> Config:
    """
    Parses command-line arguments and returns a Config object.
    """
    parser = argparse.ArgumentParser(
        description="Latency Measurements for reads on different memory levels and cache states")
    parser.add_argument('--name', type=str,
                        help="The name to save the script results under. Is saved in the kernel result dir")
    parser.add_argument(
        '--cache-state',
        type=str,
        choices=['M', 'E', 'I', 'R'],
        default='E',
        help="Cache state: 'M' (Modified), 'E' (Exclusive), 'I' (Invalid), 'R' (Read-only)"
    )

    args = parser.parse_args()

    # Convert to Config dataclass
    config = Config(
        cache_state=args.cache_state,
        test_name=args.name,
    )
    return config


def process_benchit_output(config: Config):
    # Run the compile command
    compile_cmd = [COMPILE_CMD, KERNEL_PATH,
                   f"--parameter-file={BASE_PARAMETERS_PATH}"]
    compile_process = subprocess.run(
        compile_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if compile_process.returncode != 0:
        print("Compilation failed")
        print(compile_process.stdout)
        print(compile_process.stderr)
        exit(0)

    # Run the run command
    run_cmd = [RUN_CMD, BINARY_PATH,
               f"--parameter-file={BASE_PARAMETERS_PATH}"]
    run_process = subprocess.run(
        run_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if run_process.returncode != 0:
        print("Execution failed")
        print(run_process.stderr)
        exit(0)

    # Parse the output to find the output file path
    output = run_process.stdout
    match = re.search(
        r'BenchIT: Wrote output to "(.*?)" in directory\s+"(.*?)"', output)
    if not match:
        print("Failed to parse output file path.")
        exit(0)

    filename, directory = match.groups()
    bit_file_path = os.path.join(directory, filename)

    # Read the .raw file
    if not os.path.exists(bit_file_path):
        print(f"Raw file not found: {bit_file_path}")
        exit(0)

    with open(bit_file_path, 'r') as f:
        data = f.read()

    # Extract the data section
    data_section_match = re.search(
        r'beginofdata(.*?)endofdata', data, re.DOTALL)
    if not data_section_match:
        print("Failed to find data section in the .raw file.")
        exit(0)

    data_section = data_section_match.group(1).strip()
    data_lines = data_section.split('\n')

    # Parse the data into a DataFrame
    df = pd.read_csv(StringIO('\n'.join(data_lines)),
                     sep='\t', header=None)  # Use StringIO here

    # Select and rename the columns
    custom_column_names = ['local', 'CCX', 'NUMA0',
                           'NUMA1', 'NUMA2', 'NUMA3', 'Inter-socket']
    df_selected = df.iloc[:, 1:len(custom_column_names)+1]
    df_selected.columns = custom_column_names

    # Rename the rows
    df_selected.index = ['L1', 'L2', 'L3', 'Main Memory']

    print(df_selected)
    return df_selected


def plot_latency_data(df, config: Config):
    """
    Function to plot latency data using Seaborn and Matplotlib.
    """
    # Prepare the dataframe for plotting
    # Ensure 'Memory Level' is a column in the DataFrame
    df_selected = df.reset_index().rename(columns={'index': 'Memory Level'})

    # Melt the DataFrame to a long format
    df_melted = pd.melt(df_selected, id_vars=[
                        'Memory Level'], var_name='Thread', value_name='Latency')

    # Set the aesthetic style of the plots
    sns.set_style("whitegrid")
    sns.set_context("paper", font_scale=1.5)

    # Create a figure and axis
    plt.figure(figsize=(10, 6))

    # Create a barplot
    ax = sns.barplot(x='Memory Level', y='Latency',
                     hue='Thread', data=df_melted, errorbar=None)

    # Customize the plot
    ax.set_title('Read Latencies from Different Threads')
    ax.set_xlabel('Memory Level')
    ax.set_ylabel('Latency (cycles)')

    # Move the legend outside the plot
    plt.legend(title='Threads', bbox_to_anchor=(1.05, 1), loc='upper left')

    # Tight layout to adjust for legend
    plt.tight_layout()

    # Save the figure to a file (e.g., PDF for publication quality)
    # plt.savefig(f'latency_plot_{config.cache_state}.pdf', format='pdf')

    # Show the plot (optional)
    plt.show()


def main():
    # Parse command-line arguments
    config = parse_arguments()

    # Collect or generate latency data based on configurations
    df = process_benchit_output(config)

    # Plot the latency data
    plot_latency_data(df, config)


if __name__ == "__main__":
    main()
