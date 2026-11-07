#!/bin/bash
# Build and/or serve the Lean blueprint
# Usage:
#   ./blueprint/build.sh          # build web
#   ./blueprint/build.sh serve    # build + serve at http://0.0.0.0:8000
#   ./blueprint/build.sh check    # check lean declarations

set -e

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
VENV="$PROJECT_ROOT/.blueprint-venv"

if [ ! -d "$VENV" ]; then
  echo "Creating blueprint venv..."
  uv venv "$VENV"
  uv pip install --python "$VENV" leanblueprint
  # kpsewhich shim (no system texlive needed for HTML builds)
  cat > "$VENV/bin/kpsewhich" << 'SHIM'
#!/bin/bash
name="$1"
IFS=':' read -ra PATHS <<< "${TEXINPUTS:-.}"
for dir in "${PATHS[@]}"; do
    [ -z "$dir" ] && dir="."
    [ -f "$dir/$name" ] && echo "$dir/$name" && exit 0
    [ -f "$dir/$name.tex" ] && echo "$dir/$name.tex" && exit 0
done
exit 1
SHIM
  chmod +x "$VENV/bin/kpsewhich"
fi

export PATH="$VENV/bin:$PATH"
cd "$PROJECT_ROOT"

case "${1:-web}" in
  web)
    leanblueprint web
    echo "Built. Run './blueprint/build.sh serve' to view."
    ;;
  serve)
    leanblueprint web
    leanblueprint serve
    ;;
  check|checkdecls)
    leanblueprint checkdecls
    ;;
  all)
    leanblueprint all
    ;;
  *)
    echo "Usage: ./blueprint/build.sh [web|serve|check|all]"
    exit 1
    ;;
esac
