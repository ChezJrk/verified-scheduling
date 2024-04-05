sed -i 's/"//g' $1
sed -i 's/@/"/g' $1
sed -i 's/~/\\n/g' $1
sed -i '/^COQ/d' $1
sed -i '/^make/d' $1
sed '/./,$!d' $1 > tmp
mv tmp $1
