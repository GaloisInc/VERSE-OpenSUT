#!/bin/bash

LOC=0
for f in $(find . -name "*.[c,h]");
do
    LOC=$(($LOC+$(cat $f | wc -l)))
done
echo LOC=$LOC