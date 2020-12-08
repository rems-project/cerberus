%token <int> NUM
%token <string> ID
%token TRUE FALSE
%token AT DOT STAR AMPERSAND
%token LPAREN RPAREN
%token COMMA
%token PLUS MINUS DIV
%token LT GT LE GE NE EQEQ
%token MIN MAX
%token CHAR SHORT INT LONG SIGNED UNSIGNED
%token BLOCK UNOWNED /* UNINIT */
%token EOF
%token BACKTICK
%left LT GT LE GE EQEQ NE
%left PLUS MINUS
%left DIV
%right STAR



%%
