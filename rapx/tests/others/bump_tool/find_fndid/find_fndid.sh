#!/bin/bash

keywords=(
"clone::Clone" "mem::drop" "ptr::drop_in_place" "ManuallyDrop::<std::boxed::Box<i32>>::drop"
"assume_init_drop" "alloc::dealloc" "call_mut" "copy_from_nonoverlapping("
"copy_to_nonoverlapping("
"copy_from("
"copy_to("
)
cargo rapx -mir > rapx.output 2>&1

while IFS= read -r line; do
  for keyword in "${keywords[@]}"; do
    if [[ "$line" == *"$keyword"* ]]; then
      if [[ "$line" =~ @\ Call:\ FnDid:\ ([0-9]+) ]]; then
        number="${BASH_REMATCH[1]}"
        echo "$keyword @ Call: FnDid:$number"
      fi
    fi
  done
done < rapx.output