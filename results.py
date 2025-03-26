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
    nb_proof: int = 0
    nb_elaborated: int = 0
    nb_translated: int = 0
    nb_checked: int = 0
    min: float = 0.0
    Q1: float = 0.0
    mean: float = 0.0
    Q3: float = 0.0
    max: float = 0.0

def collect_proofs(path):
    for root, dirs, files in os.walk(path, topdown=True):
            if not dirs:
                basename = os.path.basename(root)
                proofs[basename] = files
                summary[basename] = RecordBench()
                summary[basename].nb_proof = len(files)

def collect_elaboration_result(path):
    for root, dirs, files in os.walk(path, topdown=True):
            if not dirs:
                basename = os.path.basename(root)
                elab[basename] = files
                summary[basename].nb_elaborated = sum(1 for file in files if os.path.getsize(root + '/' +file) > 0)

def collect_translation_result(path):
    for root, dirs, files in os.walk(path, topdown=True):
            if not dirs:
                basename = os.path.basename(root)
                convert[basename] = files
                summary[basename].nb_translated = sum(1 for file in files if os.path.getsize(root + '/' +file) > 0)

def collect_bench_result(path):
    for root, dirs, files in os.walk(path, topdown=True):
        if not dirs:
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
                        if 'sledgehammer' in root.split(os.sep):
                            sledge_means.append(content['mean'])
                            sledge_mins.append(content['min'])
                            sledge_maxs.append(content['max'])
                        else:
                            continue
                    except JSONDecodeError:
                        continue
            basename = os.path.basename(root)
            means = [entry['mean'] for entry in data.values()]
            summary[basename].nb_checked = len(data)
            # percentile = np.percentile(means, [25, 50, 75])
            # summary[basename].Q1 = np.log(1 + np.quantile(means, 0.25))
            # summary[basename].mean = np.log(1 + np.quantile(means, 0.5))
            # summary[basename].Q3 = np.log(1 + np.quantile(means, 0.75))
            # summary[basename].min = np.log(1 + min([entry['min'] for entry in data.values()]))
            # summary[basename].max = np.log(1 + max([entry['max'] for entry in data.values()]))
            summary[basename].Q1 = np.quantile(means, 0.25) * 1000
            summary[basename].mean = np.quantile(means, 0.5) * 1000
            summary[basename].Q3 = np.quantile(means, 0.75) * 1000
            summary[basename].min = min([entry['min'] for entry in data.values()]) * 1000
            summary[basename].max = max([entry['max'] for entry in data.values()]) * 1000
            results[basename] = data

summary = dict()
proofs = dict()
elab = dict()
convert = dict()
results = dict()

sledge_means = []
sledge_mins = []
sledge_maxs = []

collect_proofs('proofs')

collect_elaboration_result('run/alethe')

collect_translation_result('run/convert')

collect_bench_result('run/results')

# Convert the dataclass objects to dictionaries and include the string key
records_for_table = [
    [key] + list(asdict(record).values())
    for key, record in summary.items()
]

# print(summary)

# Define the headers
headers = ["Record", "nb_proof", "nb_elaborated", "nb_translated", "nb_checked", "min", "Q1", "mean", "Q3", "max"]

# Print the table using tabulate
print(tabulate(records_for_table, headers=headers, tablefmt="fancy_grid", floatfmt=".3f"))


####### Fix with sledgehammer

# print(len(sledge_means))
# sledge_min = np.log(1 + min(sledge_mins))
# sledge_q1 = np.log(1 + np.quantile(sledge_means, 0.25))
# sledge_mean = np.log(1 + np.quantile(sledge_means, 0.5))
# sledge_q3 = np.log(1 + np.quantile(sledge_means, 0.75))
# sledge_max = np.log(1 + max(sledge_maxs))
# print(f'MIN = {sledge_min:.3f}  Q1 = {sledge_q1:.3f}    Mean={sledge_mean:.3f}  Q3 ={sledge_q3:.3f}     Max={sledge_max:.3f}')



# print(len(sledge_means))
# sledge_min = min(sledge_mins) * 1000
# sledge_q1 = np.quantile(sledge_means, 0.25) * 1000
# sledge_mean = np.quantile(sledge_means, 0.5) * 1000
# sledge_q3 = np.quantile(sledge_means, 0.75) * 1000
# sledge_max = max(sledge_maxs) * 1000
# print(f'MIN = {sledge_min:.3f}  Q1 = {sledge_q1:.3f}    Mean={sledge_mean:.3f}  Q3 ={sledge_q3:.3f}     Max={sledge_max:.3f}')
