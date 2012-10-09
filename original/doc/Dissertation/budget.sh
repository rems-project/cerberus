#!/bin/bash

echo "12000 - `texcount-2.3 -1 \"${1}\" | sed 's/\([0-9]\+\).*/\1/g'`" | bc
