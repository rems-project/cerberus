struct coord {
    int x;
    int y;
};


/*@

type_synonym point = { integer x, integer y }

function (struct coord) foo(point bar) {
    { x : 0 , y: 0 , ..bar }
}

@*/
