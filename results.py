#!./python

import os
import json
from pathlib import Path
from json.decoder import JSONDecodeError
import pprint as pp
import numpy as np
from tabulate import tabulate
from dataclasses import dataclass, asdict


@dataclass
class RecordBench:
    logic: str = ""
    nb_translated: int = 0
    checked: int = 0
    min: float = 0.0
    Q1: float = 0.0
    mean: float = 0.0
    Q3: float = 0.0
    max: float = 0.0

def collect_translation_result(path):
    base_path = Path(path)
    for logic_dir in os.listdir(base_path):
        logic_name = logic_dir
        logic_dir_path = os.path.join(base_path, logic_dir)

        if os.path.isdir(logic_dir_path):
            # Get level 2 directories (benchmarks)
            for benchmark in os.listdir(logic_dir_path):
                summary[benchmark] = RecordBench()
                summary[benchmark].logic = logic_name
                benchmark_path = os.path.join(logic_dir_path, benchmark)

                if os.path.isdir(benchmark_path):
                    file_count = 0

                    # Now recurse into all subdirectories under benchmarks - collect samples
                    for root, dirs, files in os.walk(benchmark_path):
                        file_count += len(files)
                    summary[benchmark].nb_translated = file_count

def collect_bench_result(path):
    base_path = Path(path)
    for logic_dir in os.listdir(base_path):
        logic_name = logic_dir
        logic_dir_path = os.path.join(base_path, logic_dir)

        if os.path.isdir(logic_dir_path):
            # Get level 2 directories (benchmarks)
            for benchmark in os.listdir(logic_dir_path):
                benchmark_path = os.path.join(logic_dir_path, benchmark)

                if os.path.isdir(benchmark_path):
                    filecorr = 0
                    # Now recurse into all subdirectories under benchmarks - collect samples
                    for root, dirs, files in os.walk(benchmark_path):
                        if len(files) > 0:
                            data = dict()
                            for file in files:
                                with open(root + '/' + file, 'r') as f:
                                    try:
                                        content = json.load(f)["results"][0]
                                        if all(v == 0 for v in content['exit_codes']):
                                            data[file] = { 
                                                'mean': content['mean'],
                                                'min': content['min'],
                                                'max': content['max'],
                                                'median': content['median']
                                            }
                                            filecorr += 1 
                                        else:
                                            continue
                                    except JSONDecodeError:
                                        continue
                            summary[benchmark].checked = filecorr
                            means = [entry['mean'] for entry in data.values()]
                            # percentile = np.percentile(means, [25, 50, 75])
                            # summary[benchmark].Q1 = np.log(1 + np.quantile(means, 0.25))
                            # summary[benchmark].mean = np.log(1 + np.quantile(means, 0.5))
                            # summary[benchmark].Q3 = np.log(1 + np.quantile(means, 0.75))
                            # summary[benchmark].min = np.log(1 + min([entry['min'] for entry in data.values()]))
                            # summary[benchmark].max = np.log(1 + max([entry['max'] for entry in data.values()]))
                            summary[benchmark].Q1 = np.quantile(means, 0.25) * 1000
                            summary[benchmark].mean = np.quantile(means, 0.5) * 1000
                            summary[benchmark].Q3 = np.quantile(means, 0.75) * 1000
                            summary[benchmark].min = min([entry['min'] for entry in data.values()]) * 1000
                            summary[benchmark].max = max([entry['max'] for entry in data.values()]) * 1000

# MAIN
if __name__ == '__main__':
    summary = dict()
    convert = dict()
    results = dict()

    collect_translation_result('run/convert')

    collect_bench_result('run/results')

    # Convert the dataclass objects to dictionaries and include the string key
    records_for_table = [
        [key] + list(asdict(record).values())
        for key, record in summary.items()
    ]

    # Define the headers
    headers = ["Record", "nb_translated", "checked", "min", "Q1", "mean", "Q3", "max"]

    # Print the table using tabulate with time in Miliseconds
    print(tabulate(records_for_table, headers=headers, tablefmt="fancy_grid", floatfmt=".3f"))
