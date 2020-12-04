%token <int> INT
%token <string> ID
%token AT
%token /* DOT */ DOTDOT /* COLON */
%token /* AMPERSAND */ STAR
%token TRUE FALSE
%token LPAREN RPAREN
%token PLUS MINUS DIV
%token LT GT LE GE /* EQ */ NE EQEQ
%token MINIMUM MAXIMUM
%token MIN_U32 MIN_U64 MAX_U32 MAX_U64 MIN_I32 MIN_I64 MAX_I32 MAX_I64
%token BLOCK UNOWNED
%token EOF
%left LT GT LE GE EQEQ NE
%left PLUS MINUS
%left DIV
%left MAXIMUM MINIMUM
%left STAR
%left DOTDOT

%%
