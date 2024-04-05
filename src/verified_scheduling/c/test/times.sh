#!/bin/zsh
#assert.sh

rm -f time.log
touch time.log

for file in *_time
do
	./$file >> time.log
done

