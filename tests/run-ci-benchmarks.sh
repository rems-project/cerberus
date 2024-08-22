#!/bin/bash

cat << EOF
[
    {
        "name": "My Custom Smaller Is Better Benchmark - CPU Load",
        "unit": "Seconds",
        "value": 500
    },
    {
        "name": "My Custom Smaller Is Better Benchmark - Memory Used",
        "unit": "Megabytes",
        "value": 100,
        "range": "3",
        "extra": "Value for Tooltip: 25\nOptional Num #2: 100\nAnything Else!"
    }
]
EOF
