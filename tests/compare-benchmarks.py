#!/usr/bin/env python3

import json
import sys
import tabulate

# Warn if the new code exceeds this percentage threshold of slowdown.
THRESHOLD = 150 # 2.5x slowdown

def to_diff(new_value, baseline_value):
    diff = new_value - baseline_value

    percent = (new_value / baseline_value - 1) * 100
    output = "{diff:+.2f} ({percent:+.2f}%)".format(diff=diff, percent=percent)

    return (output, percent)

def main():
    if len(sys.argv) != 3:
        print("usage: compare-benchmarks.py <baseline.json> <new.json>", file=sys.stderr)
        exit(-1)
    
    
    with open(sys.argv[2], 'r') as f:
        new_data = json.load(f)
    
    new_numbers = {}
    for benchmark in new_data:
        new_numbers[benchmark['name']] = benchmark['value']
    
    with open(sys.argv[1], 'r') as f:
        baseline = json.load(f)
    
    missing = set()
    degradation = set()
    baseline_total = 0
    new_total = 0
    
    output = []
    for benchmark in baseline:
        name = benchmark['name']
        baseline_value = benchmark['value']
        baseline_total += baseline_value
    
        new_value_m = new_numbers.get(name)
        if new_value_m:
            new_total += new_value_m
            (diff, percentage) = to_diff(new_value_m, baseline_value)

            if percentage > THRESHOLD:
                disp_name = "**" + name + "***"
                degradation.add(name)
            else:
                disp_name = name

            output.append([disp_name, baseline_value, new_value_m, diff])

            del new_numbers[name]
        else:
            missing.add(name)

    for name in new_numbers:
        new_value = new_numbers[name]
        output.append([name, "-", new_value, "-"])

        new_total += new_value

    (total_diff, _) = to_diff(new_total, baseline_total)
    output.append(["**Total runtime**", baseline_total, new_total, total_diff])

    print("")
    if len(degradation) != 0:
        print("**Warning**: Performance degradations: " + ', '.join(degradation))
    if len(missing) != 0:
        print("**Warning**: Removed benchmarks: " + ', '.join(missing))
    added = new_numbers.keys()
    if len(added) != 0:
        print("Added benchmarks: " + ', '.join(added))

    print("\n# Benchmark comparison\n")
    
    # Benchmark name | Old time (s) | New time (s) | Difference (s)
    print(tabulate.tabulate(output, headers=['Benchmark name', 'Baseline time (s)', 'New time (s)', 'Difference (s)'], tablefmt='pipe'))

if __name__ == "__main__":
    main()
