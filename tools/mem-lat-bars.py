import argparse
from dataclasses import dataclass
import pandas as pd
import plotly.express as px


KERNEL_PATH = "kernel/arch_x86-64/memory_latency/C/pthread/0/read"
BASE_PARAMETER_PATH = "kernel/arch_x86-64/memory_latency/C/pthread/0/read/PARAMETERS_ATHENA_1LEVELS"


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


def get_latency_data(config: Config):
    """
    Function to collect read latency data based on the cache state and other configurations.
    """
    # Simulate data collection based on cache state
    import random

    # Define cache levels and threads
    caches = ['L1 Cache', 'L2 Cache', 'L3 Cache', 'Main Memory']
    threads = [f'Thread {i+1}' for i in range(7)]  # Threads 1 to 7

    # Initialize data storage
    data = {'Memory Level': [], 'Thread': [], 'Latency (cycles)': []}

    # Collect latency data
    for cache in caches:
        for thread in threads:
            # Simulate latency values based on cache level and cache state
            base_latency = {
                'L1 Cache': random.uniform(1, 3),
                'L2 Cache': random.uniform(3, 6),
                'L3 Cache': random.uniform(6, 10),
                'Main Memory': random.uniform(50, 100),
            }[cache]

            # Adjust latency based on cache state
            state_multiplier = {
                'M': 0.9,
                'E': 1.0,
                'I': 1.2,
                'R': 1.1,
            }[config.cache_state]

            latency = base_latency * state_multiplier

            # Append data
            data['Memory Level'].append(cache)
            data['Thread'].append(thread)
            data['Latency (cycles)'].append(latency)

    # Convert to pandas DataFrame
    df = pd.DataFrame(data)
    return df


def plot_latency_data(df):
    """
    Function to plot latency data using Plotly.
    """
    # Create a grouped bar chart
    fig = px.bar(
        df,
        x='Memory Level',
        y='Latency (cycles)',
        color='Thread',
        barmode='group',
        title='Read Latencies from Different Threads',
        labels={'Latency (cycles)': 'Read Latency (cycles)',
                'Memory Level': 'Memory Hierarchy Level'}
    )

    # Update layout for better visualization
    fig.update_layout(
        xaxis_title='Memory Level',
        yaxis_title='Latency (cycles)',
        legend_title='Threads',
        font=dict(size=14)
    )

    # Display the plot
    fig.show()


def main():
    # Parse command-line arguments
    config = parse_arguments()

    # Collect or generate latency data based on configurations
    df = get_latency_data(config)

    # Plot the latency data
    plot_latency_data(df)


if __name__ == "__main__":
    main()
