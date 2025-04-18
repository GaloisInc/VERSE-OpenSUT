#!/usr/bin/env bash

usage () {
    echo "$(basename $0) [-h]"
    echo ""
    echo "Count lines of code, lines of specification, and other metrics for"
    echo "the OpenSUT and the two change events."
    echo ""
    echo "Options:"
    echo ""
    echo "-h    Print this help message."
    echo ""
}

while getopts "h" opt; do
  case $opt in
    h)
      usage
      exit 0
      ;;
    \?)
      echo "Invalid option: -$OPTARG" >&2
      exit 1
      ;;
  esac
done

shift $((OPTIND -1))

# -----------------------------------------------------------------------------
# Count specs and lines of code at a given point in git history.

# Counts lines of source code, excluding whitespace and comments.
#
# params: target files/directories
count_sloc () {
    cloc --include-lang="C,C/C++ Header" $@ | \
    grep SUM                                | \
    awk '{print $NF}'
}

# Count lines of code, but only in files that contain at least one spec.
#
# params: target files/directories
count_sloc_in_spec_files () {
    find -E $@ -regex ".*\.(c|h)" -exec grep -l "/\*$" {} ';' | \
    xargs cloc --include-lang="C,C/C++ Header"                | \
    grep SUM                                                  | \
    awk '{print $NF}'
}

# Count lines of spec
#
# params: target files/directories
count_spec_sloc () {

    # Single-line specs changed (i.e. /*$ ... $*/ on one line)
    spec_single_lines_changed=$(\
      find -E $@ -regex ".*\.(c|h)" | \
      xargs cat                     | \
      grep "\*$.*$\*"               | \
      wc -l \
    )

    # Number of lines of spec changed that span multiple lines
    spec_multilines_changed=$(\
      find -E $@ -regex ".*\.(c|h)" | \
      xargs cat                     | \
      grep -v "\*$.*$\*"            | \
      sed -n '/\*\$/,/\$\*/p'       | \
      grep -v "^\s*\$\*/\s*$"         | \
      grep -v "^\s*/\*\$\s*$"         | \
      grep -v "^\s*$"                | \
      grep -v "^\s*//"              | \
      wc -l \
    )

    echo $(($spec_single_lines_changed + $spec_multilines_changed))
}

# -----------------------------------------------------------------------------
# Measure Change Events

filter_lines_changed () {
    grep -E "^(-|\+)"
}

filter_multiline_specs () {
    grep -v "\*$.*$\*"      | \
    sed -n '/^[+-]\s*\/\*\$/,/^[+-]\s*\$\*\//p'
}

# Removes lines that only contain comments, whitespace, or spec delimiters.
remove_ws_comments () {
    grep -Ev "^(-|\+)\s*$"  | \
    grep -Ev "^(-|\+)\s*//"
    grep -v "^[+-]\s*/\*\$\s*$" | \
    grep -v "^[+-]\s*\$\*/\s*$"
}

# param 1: starting git hash
# param 2: ending git hash
count_lines_changed () {
    git diff -W $1 $2       | \
    remove_ws_comments      | \
    filter_lines_changed    | \
    wc -l
}

# param 1: starting git hash
# param 2: ending git hash
count_spec_lines_changed () {

    DIFF_FROM=$1
    DIFF_TO=$2

    # Single-line specs changed (i.e. /*$ ... $*/ on one line)
    spec_single_lines_changed=$(\
      git diff -W ${DIFF_FROM} ${DIFF_TO} | \
      grep "\*$.*$\*"                     | \
      grep -E "^(-|\+)"                   | \
      wc -l \
    )

    # Number of lines of spec changed that span multiple lines
    spec_multilines_changed=$(\
      git diff -W ${DIFF_FROM} ${DIFF_TO} | \
      filter_multiline_specs              | \
      remove_ws_comments                  | \
      filter_lines_changed                | \
      wc -l \
    )

    echo "$((${spec_multilines_changed} + ${spec_single_lines_changed}))"
}

# Measures the level of effort of a change event.
#
# param: starting git hash
# param: ending git hash
measure_change_event () {

    DIFF_FROM=$1
    DIFF_TO=$2

    rel_component_dirs="
      include
      logging
      mission_key_management
      mission_protection_system
      mkm_client
      platform_crypto"

    component_dirs=$(\
        for word in ${rel_component_dirs}; do
            echo $word | sed -e "s%^%components/%"; \
        done | xargs echo \
    )

    git checkout -q $DIFF_FROM

    sloc=$(count_sloc ${component_dirs})
    sloc_in_spec_files=$(count_sloc_in_spec_files ${component_dirs})
    spec_sloc=$(count_spec_sloc ${component_dirs})

    echo "Lines of code in all files (excludes specs): ${sloc}"
    echo "Lines of code in files with specs (excludes specs): ${sloc_in_spec_files}"
    echo ""

    echo "Lines of spec: ${spec_sloc}"
    echo "Spec overhead: $(( ${spec_sloc} * 100 / (${sloc}+${spec_sloc}) ))%"
    echo "Spec overhead (excluding files without any specs): $(( ${spec_sloc} * 100 / (${sloc_in_spec_files}+${spec_sloc}) ))%"
    echo ""

    all_lines_changed=$(count_lines_changed $DIFF_FROM $DIFF_TO)
    spec_lines_changed=$(count_spec_lines_changed $DIFF_FROM $DIFF_TO)

    echo "All  lines changed: ${all_lines_changed}"
    echo "Spec lines changed (including new specs): ${spec_lines_changed}"
    echo ""

    echo "Spec overhead in this change: $((${spec_lines_changed} * 100 / ${all_lines_changed}))%"
    echo "Spec overhead w.r.t. original effort: $(( ${spec_lines_changed} * 100 / ${spec_sloc} ))%"
}

# Make a temp dir and check out a clean copy of the repo
cwd=$(pwd)
tmp=$(mktemp -d)
echo "CREATING temporary directory: $tmp"
echo ""

cd $tmp
echo "CLONING a fresh copy of VERSE-OpenSUT"
git clone -q https://github.com/GaloisInc/VERSE-OpenSUT.git

cd VERSE-OpenSUT

echo ""
echo "CHANGE EVENT 1"
echo "--------------"
measure_change_event f21bb3ea5efb69a725784ab9624228d88f75bf08 13033a69f84213e8f3827eaef35bdba2f4e6e25f 

echo ""
echo ""

echo "CHANGE EVENT 2"
echo "--------------"
measure_change_event b25c1c164de310cbef375ae8ab9e435fb0e48396 64ed90c1b19a31aadb571554d43b1f6d8758565d

echo ""

# Clean up
cd $cwd
echo "DELETING temporary directory"
rm -rf $tmp
