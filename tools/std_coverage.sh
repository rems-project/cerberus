if [ -z $CERB_PATH ]; then
  MODEL_PATH=.
else
  MODEL_PATH=$CERB_PATH/model
fi

if [ -z $CERB_PATH ]; then
  PARSER_PATH=.
else
  PARSER_PATH=$CERB_PATH/parsers
fi

if [ -z $CERB_PATH ]; then
  CORELIB_PATH=.
else
  CORELIB_PATH=$CERB_PATH/include/core
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

grep -HnER "STD|std" $MODEL_PATH $PARSER_PATH $CORELIB_PATH | awk ''"$FILTER"'' | sort
