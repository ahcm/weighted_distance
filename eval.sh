#!/usr/bin/env zsh
tsvfile=$1
search_terms_file=$2
name=$3

if [ ! -r $tsvfile ] || [ ! -r $search_terms_file ]; then
    echo "Need a filename"
    exit 1
fi

mkdir -p $name
LANG=de_DE
time while read a; do
    ./weighted_distance -h weight_table.a -m -t -i -n 3 "$a" $tsvfile > "$name/$a"
done < $search_terms_file
cat "$name"/* | ./accumulate > "$name.dat"

