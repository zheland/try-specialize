#!/usr/bin/env bash

for module in "--test optimized"; do
    output=$(
        cargo +nightly rustc \
        --release \
        --message-format=json-render-diagnostics \
        $module \
        -- \
        --emit=llvm-ir \
        --emit=asm
    )
    artifact=$(
        echo "$output" \
        | rg -o "[^\"]*/release/deps/[0-9a-z_-]*" \
        | tail -n1
    )
    echo -e "\e]8;;file://$artifact.s\e\\$artifact.s\e]8;;\e\\"
    echo -e "\e]8;;file://$artifact.ll\e\\$artifact.ll\e]8;;\e\\"
done
