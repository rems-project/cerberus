#!/usr/bin/env bash
cerberus "$@" 2> >(sed '/^Time spent:/d' >&2)
