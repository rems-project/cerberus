#!/usr/bin/env bash
cerberus "$@" 2> >(tail -n +9 | sed '/\((debug 1):\)\|\(Core typechecking\)/d')
