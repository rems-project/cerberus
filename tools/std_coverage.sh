if [ -z $CERB_PATH ]; then
  MODEL_PATH=.
else
  MODEL_PATH=$CERB_PATH/model
fi

FILTER='
  BEGIN {
    FS=":"
    OFS=":"
  }

  {
    n = split ($1, file, "/")
    if (match($3, /§[0-9]+(\.[0-9]+)*(#[0-9])*(,? sentence(s?) [0-9]+(-[0-9])?)*/))
      print substr($3, RSTART, RLENGTH), file[n], $2
  }
'

grep -HnER "STD|std" $MODEL_PATH | awk ''"$FILTER"'' | sort
