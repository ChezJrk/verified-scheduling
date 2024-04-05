#!/bin/zsh
#assert.sh


for file in *eq
do
	./$file &> /dev/null
	if [ $? -ne 0 ]  
	then echo -e "\e[39m$(basename $file _eq)\t \e[91mfailed"
	else echo -e "\e[39m$(basename $file _eq)\t \e[92mpassed"
	fi
done

echo -e "\e[39m"
