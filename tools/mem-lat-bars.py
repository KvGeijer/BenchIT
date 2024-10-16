import argparse
import shutil
import subprocess
import re
import os
import datetime
from dataclasses import dataclass
import pandas as pd
import seaborn as sns
import matplotlib.pyplot as plt
from io import StringIO
from functools import wraps
from pathlib import Path
import random
import string


KERNEL_PATH = "./kernel/arch_x86-64/memory_latency/C/pthread/0/read"
BINARY_PATH = "./bin/arch_x86-64.memory_latency.C.pthread.0.read.0"
WANTED_PARAMETERS_PATH = "kernel/arch_x86-64/memory_latency/C/pthread/0/read/PARAMETERS_ATHENA_1LEVELS"
PARAMETERS_PATH = "kernel/arch_x86-64/memory_latency/C/pthread/0/read/PARAMETERS"
COMPILE_CMD = "./COMPILE.SH"
RUN_CMD = "./RUN.SH"


@dataclass
class Config:
    save_name: Path | None
    old_name: Path | None
    cache_state: str
    dynamic_threads: bool


def parse_arguments() -> Config:
    """
    Parses command-line arguments and returns a Config object.
    """
    parser = argparse.ArgumentParser(
        description="Latency Measurements for reads on different memory levels and cache states")
    parser.add_argument('--save-name', type=str,
                        help="A name to save the script results under. Is saved in the kernel output/mem-lat-bars dir")
    parser.add_argument(
        '--cache-state',
        type=str,
        choices=['M', 'E', 'I', 'S', 'F', 'O', 'U'],
        default='E',
        help="Cache state: 'M' (Modified), 'E' (Exclusive), 'I' (Invalid), 'S' (Shared), 'F' (Forwarded), 'O' (Owned), 'U' (Undefined)"
    )
    parser.add_argument('--dynamic-thread-names', action='store_true',
                        help="Uses the core ids instead of hard-coded names based on distance.")
    parser.add_argument('--old-name', type=str,
                        help="Re-uses old data from a specific results directory, from an earlier run of this test.")

    args = parser.parse_args()
    if args.save_name:
        save_name = Path('output/mem-lat-bars') / args.save_name
        if save_name.exists():
            now = datetime.datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
            save_name = save_name.with_name(f"{save_name.name}_{now}")
    else:
        save_name = None

    if args.old_name:
        old_name = Path(args.old_name)
        if not old_name.exists():
            print("Old name does not point to a directory!")
            exit(0)
    else:
        old_name = None

    # Convert to Config dataclass
    config = Config(
        cache_state=args.cache_state,
        save_name=save_name,
        dynamic_threads=args.dynamic_thread_names,
        old_name=old_name,
    )
    return config


def parse_cpu_list():
    """
    Parses the cores/cpus used in the experiment, by reading the parameter file 
    """
    with open(PARAMETERS_PATH, 'r') as file:
        for line in file:
            # Find the line starting with BENCHIT_KERNEL_CPU_LIST
            if line.startswith("BENCHIT_KERNEL_CPU_LIST"):
                # Use regex to extract the numbers inside the quotes
                match = re.search(r'"([\d, ]+)"', line)
                if match:
                    # Extract the matched string and remove spaces
                    cpu_list_str = match.group(1).replace(" ", "")
                    # Split the string by commas and convert to a list of integers
                    cpu_list = cpu_list_str.split(',')
                    return cpu_list
    print("Warning: Could not parse out the cpus used in the parameter file")
    return None


def local_parameters(func):
    """
    Wraps a function, to replace PARAMETERS with the wanted one temporarily, in the end restoring the original state.
    So you can make any changes you want to the parameters file.
    """
    @wraps(func)
    def wrapper(*args, **kwargs):
        # Generate a random extension
        random_ext = ''.join(random.choices(
            string.ascii_lowercase + string.digits, k=8))
        used_dir, used_filename = os.path.split(PARAMETERS_PATH)
        used_base, used_ext = os.path.splitext(used_filename)
        backup_filename = f"{used_base}.{random_ext}"
        backup_path = os.path.join(used_dir, backup_filename)

        try:
            # Copy the used parameters file to a backup with a random extension
            shutil.copy2(PARAMETERS_PATH, backup_path)

            # Replace the used parameters file with the wanted parameters file
            shutil.copy2(WANTED_PARAMETERS_PATH, PARAMETERS_PATH)

            # Execute the wrapped function
            result = func(*args, **kwargs)
            return result

        finally:
            # Restore the original used parameters file
            if os.path.exists(backup_path):
                shutil.move(backup_path, PARAMETERS_PATH)
                pass
            else:
                print(
                    f"ERROR: Backup file '{backup_path}' not found. Original PARAMETERS file not restored!")

    return wrapper


@local_parameters
def process_benchit_output(config: Config):
    # Change the cache state
    with open(PARAMETERS_PATH, 'r') as file:
        content = file.read()

    with open(PARAMETERS_PATH, 'w') as file:
        new_content = re.sub(r'BENCINT_KERNAL_USE_MODE="."',
                             f'BENCINT_KERNAL_USE_MODE="{config.cache_state}"', content)
        file.write(new_content)

    # Run the compile command
    compile_cmd = [COMPILE_CMD, KERNEL_PATH]
    compile_process = subprocess.run(
        compile_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if compile_process.returncode != 0:
        print("Compilation failed")
        print(compile_process.stdout)
        print(compile_process.stderr)
        exit(0)

    # Run the run command
    run_cmd = [RUN_CMD, BINARY_PATH]
    run_process = subprocess.run(
        run_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if run_process.returncode != 0:
        print("Execution failed")
        print(run_process.stdout)
        print(run_process.stderr)
        exit(0)

    # Parse the output to find the output file path
    output = run_process.stdout
    match = re.search(
        r'BenchIT: Wrote output to "(.*?)" in directory\s+"(.*?)"', output)
    if not match:
        print("Failed to parse output file path.")
        print(run_process.stdout)
        print(run_process.stderr)
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
    if config.dynamic_threads:
        custom_column_names = parse_cpu_list()
    else:
        custom_column_names = ['local', 'hyperthread', 'CCX', 'NUMA0',
                               'NUMA1', 'NUMA2', 'NUMA3', 'Inter-socket']
    df_selected = df.iloc[:, 1:len(custom_column_names)+1]
    df_selected.columns = custom_column_names

    # Rename the rows
    df_selected.index = ['L1', 'L2', 'L3', 'Main Memory']

    if config.save_name:
        os.makedirs(config.save_name, exist_ok=True)
        data_path = os.path.join(config.save_name, 'data.csv')
        df_selected.to_csv(data_path)

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

    # Save the figure to a file
    if config.save_name:
        os.makedirs(config.save_name, exist_ok=True)
        figure_path = os.path.join(config.save_name, 'figure.pdf')
        plt.savefig(figure_path, format='pdf')

    # Show the plot
    plt.show()


def main():
    # Parse command-line arguments
    config = parse_arguments()

    if not config.old_name:
        try:
            # Disable prefetching for the experiments
            disable_prefetch()

            # Collect or generate latency data based on configurations
            df = process_benchit_output(config)
        finally:
            # Don't forget to re-enable the prefetching
            enable_prefetch()
    else:
        data_path = config.old_name / 'data.csv'
        if not data_path.is_file():
            print("Old data does not exist in folder")
            exit(0)
        df = pd.read_csv(data_path, index_col=0)

    # Plot the latency data
    plot_latency_data(df, config)


def disable_prefetch():
    # Disable pre-fetching using msr.sh from https://github.com/KvGeijer/msr-utils/tree/main
    msr_path = shutil.which("msr.sh")

    if msr_path:
        try:
            subprocess.run(
                [msr_path, "--prefetch", "disable"], check=True)
        except subprocess.CalledProcessError as e:
            print(f"WARNING: Could not disable prefetching! {e}")
    else:
        print("WARNING: Could not disable pre-fetching, so results for L1 are probably off")


def enable_prefetch():
    # Enable pre-fetching using msr.sh from https://github.com/KvGeijer/msr-utils/tree/main
    msr_path = shutil.which("msr.sh")

    if msr_path:
        try:
            subprocess.run(
                [msr_path, "--prefetch", "enable"], check=True)
        except subprocess.CalledProcessError as e:
            print(f"WARNING: Could not re-enable prefetching! {e}")


if __name__ == "__main__":
    main()
