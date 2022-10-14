ps -o comm= -p $$

VF_RW_WD=`pwd`
SOURCE_FILE="$1"
BACKUP_IDX=0

echo "VF RW: 'long unsigned int' -> 'unsinged long int'"
echo "backup : $VF_RW_WD/$SOURCE_FILE.backup-$BACKUP_IDX"
echo backup index $BACKUP_IDX
sed -i."backup-$BACKUP_IDX" 's|long unsigned int|unsigned long int|g' $SOURCE_FILE
((BACKUP_IDX=BACKUP_IDX+1))
echo backup index $BACKUP_IDX
