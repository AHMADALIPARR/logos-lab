# Source this to put dotnet and Boogie on PATH.
export DOTNET_ROOT="${DOTNET_ROOT:-$HOME/.dotnet}"
export PATH="$DOTNET_ROOT:/workspace/.tools/boogie:$PATH"
export Z3="${Z3:-/workspace/.tools/dafny/z3/bin/z3-4.12.1}"
