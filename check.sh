#!/usr/bin/env bash

# ================================================================
# Crate-specific settings
# ================================================================

toolchains_param_set=(
    "stable|"
    "beta|"
    "nightly|--features __test_nightly"
    "1.82.0|"
)
all_features=( "" "alloc" "std" "unreliable" )
test_opt_level1_args="--release --features alloc,std,unreliable"
test_opt_level2_args="--release --features alloc,std,unreliable"
test_opt_level2_args+=",__test_extern_fn_merging,__test_extern_fn_dce"
cross_targets=(
    "i686-unknown-linux-gnu"
    "x86_64-unknown-linux-gnu"
    "aarch64-unknown-linux-gnu"
    "i686-pc-windows-gnu"
    "wasm32-unknown-emscripten"
)
cross_args="--features alloc,std,unreliable"
min_covered_functions_percent=95
min_covered_lines_percent=90
min_covered_regions_percent=90
crate_docs_link="https://docs.rs/try-specialize/latest/try_specialize"
crate_docs_ignored_lines_regex=$'^(L|T) \[`transmute`\]: .*$'

# ================================================================
# Common check script code
# ================================================================

set -Eeuo pipefail

tmp_dir=""
bold_red=$'\033[1;31m'
bold_green=$'\033[1;32m'
no_color=$'\033[0m'

cleanup() {
    local return_code=$?
    if [ -n "$tmp_dir" ]; then
        rm -rf -- "$tmp_dir"
    fi
    exit $return_code
}

trap cleanup EXIT

tmp_dir="$( mktemp -d )"

exec() { "$@"; }
passthru() { tee; }
comment() { tee; }
ok() { echo "${bold_green}OK${no_color}: $@" 1>&2; }
fail() { echo "${bold_red}ERROR${no_color}: $@" 1>&2; exit 1; }
echo_and_run() { echo "$ ${*@Q}"; "$@"; }

echo_and_try_run() {
    set +eo pipefail
    echo "$ ${*@Q}"
    "$@" 2> >( tee "$tmp_dir/error.txt" )
    echo $? > "$tmp_dir/return_code.txt"
    set -eo pipefail
}

expect_failure() {
    if [ "$(cat "$tmp_dir/return_code.txt")" -ne "0" ]; then
        ok "Command failed as expected."
        if ! cat "$tmp_dir/error.txt" | grep -q "$@"; then
            fail "Unexpected error message, expected regex: ${*@Q}."
        fi
    else
        fail "Command did not fail as expected."
    fi
}

# Apply some transformations to lib.rs and README.md, to get the documentation
# in a single intermediate format, which is expected to be the same for both:
# lib.rs and README.md.
normalize_docs() {
    source=$1
    local libdoc=false
    local readme=false
    if [[ $source == "lib.rs" ]]; then
        libdoc=exec
        readme=passthru
    elif [[ $source == "README.md" ]]; then
        libdoc=passthru
        readme=exec
    else
        fail "Internal script error: invalid docs source."
    fi

    set +eo pipefail

    cat \
        | comment "Remove title and badges from README.md" \
        | $readme awk '
            BEGIN { is_content=0 }
            is_content==1 { print; next }
            /^(# .*||!\[.*|\[!\[.*)$/ { next } # Ignore title, empty line and images.
            is_content==0 { is_content=1; print; next }
        ' \
        | comment "Remove '//!' lines from lib.rs" \
        | $libdoc rg '^//!' \
        | $libdoc rg '^//! ?' -r '' \
        | comment "Add "C " prefix for markdown code lines." \
        | comment "Add "T " prefix for other markdown lines." \
        | awk '
            BEGIN { is_code=0 }
            /^```.*$/ { print "C " $0; is_code=!is_code; next }
            is_code==0 { print "T " $0; next }
            is_code==1 { print "C " $0; next }
        ' \
        | comment "Remove hidden portions from lib.rs doc examples." \
        | $libdoc rg -v $'^C #( |$)' \
        | comment "Decrease all headers level in README.md." \
        | $readme rg --passthru $'^T #(#+) (.*)' -r $'T $1 $2' \
        | comment "Convert rust stdlib links to rust paths in README.md." \
        | comment "Use "L " prefix for markdown lines with link references." \
        | $readme rg --passthru \
            $'^T \[(.*)\]: https://doc\.rust-lang\.org/(std|core)/(?:(?:(?:([^/]*)/)?([^/]*)/)?([^/]*)/)?(?:struct|enum|trait|fn|primitive|macro)\.([^/]*)\.html(#| |$)' \
            -r $'L [$1]: $2::$3::$4::$5::$6$7' \
        | comment "Convert rust stdlib module links to rust paths in README.md." \
        | $readme rg --passthru \
            $'^T \[(.*)\]: https://doc\.rust-lang\.org/(std|core)/(?:(?:(?:([^/]*)/)?([^/]*)/)?([^/]*)/)?index\.html(#| |$)' \
            -r $'L [$1]: $2::$3::$4::$5$6' \
        | comment "Convert crate links to rust paths in README.md." \
        | $readme rg --passthru \
            $'^T \[(.*)\]: '"$crate_docs_link"$'/(?:(?:(?:([^/]*)/)?([^/]*)/)?([^/]*)/)?(?:struct|enum|trait|fn|primitive|macro)\.([^/]*)\.html(#| |$)' \
            -r $'L [$1]: $2::$3::$4::$5$6' \
        | comment "Convert crate module links to rust paths in README.md." \
        | $readme rg --passthru \
            $'^T \[(.*)\]: '"$crate_docs_link"$'/(?:(?:(?:([^/]*)/)?([^/]*)/)?([^/]*)/)?index\.html(#| |$)' \
            -r $'L [$1]: $2::$3::$4$5' \
        | comment "Remove artifact "::::" and starting "::" in paths after the previous link convertions." \
        | $readme rg --passthru \
            $'^L \[(.*)\]: ([^:]*)::(?:::)+' -r $'L [$1]: $2::' \
        | $readme rg --passthru \
            $'^L \[(.*)\]: ::' -r $'L [$1]: ' \
        | comment "Convert link methods to rust paths in README.md." \
        | $readme rg --passthru \
            $'^L \[(.*)\]: (.*)#method\.' -r $'L [$1]: $2$3::' \
        | comment "Remove link titles that now duplicates rust path in README.md." \
        | $readme rg --pcre2 --passthru \
            $'^L \[(.*)\]: ([^ ]*) "\\2"' -r $'L [$1]: $2' \
        | comment "Remove link references that now duplicates rust path in README.md" \
        | $readme rg --pcre2 -v $'^L \[`(.*)`\]: \\1$' \
        | $readme rg -U --pcre2 --passthru $'^(L .*)\nT \n(?:T \n)+(L .*)$' -r $'$1\n\n$2' \
        | comment "Ignore specified lines" \
        | rg -v "$crate_docs_ignored_lines_regex" \
        | comment "Remove temporary prefixes." \
        | rg --passthru $'T ' -r '' \
        | rg --passthru $'C ' -r '' \
        | rg --passthru $'L ' -r '' \
        | tee

    set -eo pipefail
}

echo_and_run cargo +nightly fmt --all -- --check
echo_and_run cargo outdated --exit-code 1

readme="$( cat README.md | normalize_docs "README.md" )"
libdoc="$( cat src/lib.rs | normalize_docs "lib.rs" )"
echo_and_run git diff <(echo "$readme") <(echo "$libdoc")

# Each value is a set of `|`-separated values:
# - comma separated features,
# - expected status on non-nightly toolchains,
# - expected status on nightly toolchain,
# - expected error message regex"
valid_no_alloc_and_no_std_param_sets=(
    "|fail|fail|panic_handler.* function required"
    "panic-handler|ok|fail|undefined symbol: rust_eh_personality"
    "alloc,panic-handler|fail|fail|no global memory allocator found"
    "alloc,panic-handler,global-allocator|ok|fail|undefined symbol: rust_eh_personality"
    "alloc,std,panic-handler,global-allocator|fail|fail|found duplicate lang item .*panic_impl"
    "alloc,std,global-allocator|ok|ok|"
)
for toolchain_params in "${toolchains_param_set[@]}"; do
    toolchain=$(echo "$toolchain_params" | cut -sd"|" -f1)
    (
        echo_and_run export CARGO_TARGET_DIR="target/check-no-alloc-and-no-std-$toolchain"
        for param_set in "${valid_no_alloc_and_no_std_param_sets[@]}"; do
            features=$(echo "$param_set" | cut -sd"|" -f1)
            expected_default=$(echo "$param_set" | cut -sd"|" -f2)
            expected_nightly=$(echo "$param_set" | cut -sd"|" -f3)
            expected_error_regex=$(echo "$param_set" | cut -sd"|" -f4-)
            if [ "$toolchain" = "nightly" ]; then
                expected="$expected_nightly"
            else
                expected="$expected_default"
            fi
            args="--config build.rustflags=[\"-C\",\"link-arg=-nostartfiles\"]"
            args+=" --manifest-path tests/no-alloc-and-no-std/Cargo.toml"
            args+=" --no-default-features"
            [ -n "$features" ] && args+=" --features $features"
            if [[ "$expected" == "ok" ]]; then
                echo_and_run cargo "+$toolchain" clippy $args -- -D warnings
                echo_and_run cargo "+$toolchain" build $args
            elif [[ "$expected" == "fail" ]]; then
                echo_and_try_run cargo "+$toolchain" build $args
                expect_failure "$expected_error_regex"
            else
                fail "Internal script error: invalid expected result."
            fi
        done
    )
done

num_features=${#all_features[@]}
num_combinations=$(echo "2^$num_features" | bc)
feature_sets=()

# Iterate over all `2^num_features` features combinations if required
# `combination_idx` is used as a bitmask of the enabled features.
for ((combination_idx = 0; combination_idx < num_combinations; combination_idx++)); do
    features_set=()
    for ((feature_idx = 0; feature_idx < num_features; feature_idx++)); do
        mask=$(echo "2^$feature_idx" | bc) # The mask of `feature_idx`-th feature.

        if (( combination_idx & mask )); then
            features_set+=(${all_features[$feature_idx]})
        fi
    done
    features=$(echo "${features_set[@]}" | tr " " ",")
    feature_sets+=("$features")
done


for toolchain_params in "${toolchains_param_set[@]}"; do
    toolchain=$(echo "$toolchain_params" | cut -sd"|" -f1)
    toolchain_flags=$(echo "$toolchain_params" | cut -sd"|" -f2)
    (
        echo_and_run export CARGO_TARGET_DIR="target/check-$toolchain"
        for features in "${feature_sets[@]}"; do
            cargo="cargo +$toolchain"
            if [ -n "$features" ]; then
                args="--no-default-features --features $features"
            else
                args="--no-default-features"
            fi
            [ -n "$toolchain_flags" ] && args+=" $toolchain_flags"
            echo_and_run $cargo clippy --all-targets $args -- -D warnings
            echo_and_run $cargo build --all-targets $args
            echo_and_run $cargo test --all-targets $args
            echo_and_run $cargo test --release --all-targets $args
            echo_and_run $cargo test --doc $args
            echo_and_run $cargo test --doc --release $args
            if [[ "$toolchain" == "nightly" ]]; then
                echo_and_run $cargo miri test --all-targets $args
            fi
            echo_and_run $cargo bench --no-run --all-targets $args
        done
    )
    (
        args="$test_opt_level1_args"
        echo_and_run export CARGO_PROFILE_RELEASE_OPT_LEVEL=1
        echo_and_run cargo test --all-targets $args
    )
    (
        args="$test_opt_level2_args"
        echo_and_run export CARGO_PROFILE_RELEASE_OPT_LEVEL=2
        echo_and_run cargo test --all-targets $args
    )
    for target in "${cross_targets[@]}"; do
        args="--target $target $cross_args"
        echo_and_run cross clippy $args -- -D warnings
        echo_and_run cross build $args
        echo_and_run cross test $args
    done
done

for features in "${feature_sets[@]}"; do
    args=()
    features=$( echo "$features" | tr "," " " )
    for feature in ${features}; do
        args+=( --features )
        args+=( $feature )
    done
    echo_and_run cargo semver-checks --only-explicit-features "${args[@]}"
done

echo_and_run cargo deny --workspace --all-features check

echo_and_run cargo +nightly llvm-cov --doctests --all-features --html \
    --fail-under-functions $min_covered_functions_percent \
    --fail-under-lines $min_covered_lines_percent \
    --fail-under-regions $min_covered_regions_percent

ok "All checks succeeded." 1>&2
