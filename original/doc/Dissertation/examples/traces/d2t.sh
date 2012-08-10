#!/bin/bash

/usr/bin/dot2tex --codeonly -ftikz -c -t math --autosize "${1}.dot" > "${1}.tikz"
