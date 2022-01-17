sed -i 's/\\n/\'$'\n''/g' $1
sed -i 's/"//g' $1
sed -i 's/@/"/g' $1
sed -i 's/~/\\n/g' $1
vim -c "%s/COQ.*//g" -c "%s/\\$//g" -c wq $1
sed '/./,$!d' $1 > tmp
mv tmp $1
csplit --quiet --elide-empty-files --suffix-format='%d.out' $1 '/!!!/' '{*}'

out_to_c() {
	sed -i '1d' $1

	NAME=$(head -n 1 $1)

	tail -n +2 $1 > $NAME

	vim -c "normal gg=G" -c wq $NAME

	rm $1
}

for f in *.out; do out_to_c $f; done
