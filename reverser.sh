#!/bin/bash

# Read from stdin or a file passed as an argument
input_stream="${1:-/dev/stdin}"

# Reverse order of proof statements
tac $input_stream -r  -s ';\|;\\n\|pseudo-Boolean proof version 3.0'
