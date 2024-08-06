/*-------------------------------------------------------------------------

	Version 		:	2.01 , ANSI standard C
	Written by		:	Stephen Fitzgerald , Jan 31, 1993
	Last Modified	:	Feb 2, 1993


	parseTree.c :- This file contains an arithmetic expression parser.

	This parser creates a parse tree for an expression which can then
	be evaluated very quickly. It is best suited to applications where
	the function must be re-evaluated many times, such as a graphing
	program. There is another version of the parser that does not
	create a parse tree but returns a long double value directly, it is
	better suited for applications that only need to evaluate the
	function a few times. ( see singleParse.c )

	The steps to use the parse tree version of the parser are :

		1. 	Input the string to be parsed. Do not include any portion
			of the string that would occur before the assignment ,'=',
			such as "f(t) =". i.e. if you had f(t) = 56*8^2 you would
			pass the parser "56*8^2" only.

			ex:
				char string[80] ;

				scanf(" %s ", string ) ;

		2.	Parse the string using parse. This creates a PARSETREE .
			parse() takes a handle to a char and updates it to point to the
			last character parsed. This is usefull when detecting errors.
			You should make a copy of your string pointer as shown,
			and hand its address to parse() .

			ex :
				#include"ParseTree.h"
				void *tree ;
				char *temp ;
				int err ;
				char errstr[160] ;

				temp = string ;
				tree = parse( &temp, &err, errstr ) ;

				if ( err ) {
					printf("%s \n ", errstr ) ;
				}

			If parse sets err non-zero then there has been a syntax
			error. The error message errstr should be printed. This will
			show the user what & where the error is.

		3. 	To evaluate the expression you pass the pointer 'tree' to eval()
			after setting any variables you want with setVariable().
			The integer err be non-zero if an error occurs during evaluation.
			ex:

				long double value, time ;

				setVariable( "t", time ) ;
				value = eval( tree, &err ) ;

				if ( errcode ) {
				|*---------------------------------------------
				 there has been an error such as divide by zero
				 See parseTree.c for a list of errors
				-----------------------------------------------*|
				}

------------------------------------------------------------------------*/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <strings.h>
#include "parseTree.h"
/*------------------------------------------------------------------------
	Define MAIN as 1 for a test program.
-------------------------------------------------------------------------*/
#define MAIN 1
#define DEBUG 0

#define isspace(c) ((c) == ' ')
#define isdigit(c) (((c) >= '0') && ((c) <= '9'))
#define advance(n) Str += (n)

#define NoOp -9999
#define BINOP 1
#define UNOP 2
#define NUM 3
#define FUNC 4
#define CONST 9999
#define VarNotFound -1

#define E 2.71828182845904523536
#define PI 3.14159265358979323846
#define PI2 1.5707963268

#define NUMRATOR 23
#define FUNCSTART 15 /*----------------------------------------------- \
						 Index of the 1st function name in the array   \
					 ------------------------------------------------*/

static char *OPRATOR[] = {
	"!", "&&", "||", "<=", "<",
	">=", ">", "==", "!=", "+",
	"-", "*", "%", "/", "^",
	"sin", "cos", "tan", "exp", "log",
	"ln", "sqrt", "step", "", "",
	"", "", "", "", ""};

/*------------------------------------------------------------------------
	Variables, names should not conflict with function names, i.e. a
	variable with the name 'exponent' will be parsed as the function
	exp() and there will be a missing parenthesis error. A variable
	with the name ex will be found OK only if it occurs before 'e'
	in the variable array. Note that 'pi' is after to 'pi/2', this
	is to insure that searches for pi/2 dont get stopped at pi. This
	is a short coming of this code and it will be fixed in a later
	version.
-------------------------------------------------------------------------*/

typedef struct var
{
	char *name;
	long double val;
} VarType;

static int MAX_VAR = 10;
static int num_var = 5;

static VarType VARIABLE[] = {
	"t",
	0.0,
	"T",
	0.0,
	"e",
	E,
	"pi",
	PI,
	"  ",
	0.0,
	"  ",
	0.0,
	"  ",
	0.0,
	"  ",
	0.0,
	"  ",
	0.0,
};

/*------------------------------------------------------------------------
	EvalErr is a flag that was available to the calling function. It is
	non zero if an error occured during the expression evaluation.  New
	versions ( >= 1.01 ) pass this value rather than have a global
	variable.
-----------------------------------------------------------------------*/
static int EvalErr = 0;

typedef struct nodeRecord
{
	int type;
	int opratorid;
	struct nodeRecord *left, *right;
	long double oprand;

} node, *PARSETREE;

static char *Str;
static char *Start_str;

static char err1Message[255];
static char err2Message[255];
static int ParseError;

static int getVarID(char *);
static PARSETREE binOpNode(int, PARSETREE, PARSETREE);
static PARSETREE unarOpNode(int, PARSETREE);
static PARSETREE numNode(int, long double);
static int evalerr(int);
static long double _eval(PARSETREE);
static void error(char *);
static long double step(long double);
static int match(char *);
static PARSETREE expr(void);
static PARSETREE term(void);
static PARSETREE fact(void);
static PARSETREE part(void);
static PARSETREE part2(void);
static long double myAtof(void);
static PARSETREE get_constant(void);
static PARSETREE func(void);

/************************.variable handling stuff.************************\

	getVarID( char *s ) returns the index of the variable named by the
	string 's' in the array VARIABLE[]. The value of the variable can
	then be found at any time with VARIABLE[ id ].val.

	SetVariable( char *s, long double v ) calls getVarID to find the variable
	and then it sets the value of the named variable to the value of 'v'.

	Both routines return 9999 if the variable does not exist.

\*-----------------------------------------------------------------------*/

static int getVarID(char *s)
{
	int i = 0;

	while (i < num_var)
	{
		if (strcmp(s, VARIABLE[i].name) == 0)
		{
			break;
		}
		else
		{
			i++;
		}
	}

	if (i < num_var)
	{
		return (i);
	}
	else
	{
		return (VarNotFound);
	}
}

int setVariable(char *s, long double v)
{
	int id;

	id = getVarID(s);

	if (id != VarNotFound)
	{
		VARIABLE[id].val = v;
		return (id);
	}
	else
	{
		return (VarNotFound);
	}
}

/************************ noderoutines  **********************************\
	A union should be used to avoid wasting space. When the left/right
	fields are in use the oprand field is not, and vise-versa.
\*-----------------------------------------------------------------------*/
void disposParseTree(void *p)
{
	PARSETREE n;

	n = (PARSETREE)p;

	if (n != NULL)
	{
		disposParseTree(n->left);
		disposParseTree(n->right);
		free(n);
	}
}

static PARSETREE binOpNode(int opor, PARSETREE lopand, PARSETREE ropand)
{
	PARSETREE n = NULL;

	if (lopand == NULL || ropand == NULL)
	{
		; /* do nothing */
	}
	else
	{
		n = (PARSETREE)malloc(sizeof(node));
		if (n != NULL)
		{
			n->type = BINOP;
			n->opratorid = opor;
			n->left = lopand;
			n->right = ropand;
			n->oprand = (long double)0.0;
		}
	}

	return (n);
}

static PARSETREE unarOpNode(int opor, PARSETREE lopand)
{
	PARSETREE n = NULL;

	if (lopand == NULL)
	{
		; /* do nothing */
	}
	else
	{
		n = (PARSETREE)malloc(sizeof(node));
		if (n != NULL)
		{
			n->type = UNOP;
			n->opratorid = opor;
			n->left = lopand;
			n->right = NULL;
			n->oprand = (long double)0.0;
		}
	}

	return (n);
}

static PARSETREE numNode(int id, long double rand)

{
	PARSETREE n = NULL;

	n = (PARSETREE)malloc(sizeof(node));

	if (n != NULL)
	{
		n->type = NUM;
		n->opratorid = id;
		n->left = NULL;
		n->right = NULL;
		n->oprand = rand;
	}

	return (n);
}

/*********************** tree evaluateing stuff  *************************\
	Evaluates a PARSETREE created by 'parse()'. If an error occurs
	ErrorCode is set and the function continues. This should be changed
	to halt the function on errors. ErrorCode is available to the calling
	function.
\*-----------------------------------------------------------------------*/

/*---------------------------------------------------
	EPSILON is the value used for zero. Any number
	less than this is considered zero.
---------------------------------------------------*/
static long double EPSILON = 5e-16;

static int evalerr(int i)
{
	EvalErr = i;
	return i;
}

long double eval(void *p, int *err_num)
{
	long double temp;
	PARSETREE n;

	n = (PARSETREE)p;

	if (n == NULL)
	{
		*err_num = 99; /* set tree-no-good code */
		return (0);
	}
	else
	{
		evalerr(0); /* reset error code */
		temp = _eval(n);
		*err_num = EvalErr;
		return (temp);
	}
}

static long double _eval(PARSETREE n)
{
	long double op1 = 0.0, op2 = 0.0, temp = 0.0;
	//	long double step() ;

	if (n == NULL)
	{
		; /* do nothing */
	}
	else
	{
		switch (n->type)
		{
		case BINOP:
			op1 = _eval(n->left);
			if (EvalErr)
				return (0);
			op2 = _eval(n->right);
			if (EvalErr)
				return (0);
			temp = 0.0;
			switch (n->opratorid)
			{
			case 0:
				evalerr(1);
				break;
			case 1:
				temp = (op1 && op2);
				break;
			case 2:
				temp = (op1 || op2);
				break;
			case 3:
				temp = (op1 <= op2);
				break;
			case 4:
				if (op1 < op2)
					temp = 1.0;
				break;
			case 5:
				temp = (op1 >= op2);
				break;
			case 6:
				temp = (op1 > op2);
				break;
			case 7:
				temp = (op1 == op2);
				break;
			case 8:
				temp = (op1 != op2);
				break;
			case 9:
				temp = (op1 + op2);
				break;
			case 10:
				temp = (op1 - op2);
				break;
			case 11:
				temp = (op1 * op2);
				break;
			case 12:
				temp = (long double)((long)op1 % (long)op2);
				break;
			case 13:
				if (op2 != 0.0)
				{
					temp = (op1 / op2);
				}
				else
				{
					evalerr(2);
				}
				break;
			case 14:
				temp = pow(op1, op2);
				break;
			default:
				evalerr(3);
				break;
			} /* switch( n->opratorid ) */
			break;
		case UNOP:
			op1 = _eval(n->left);
			if (EvalErr)
				return (0);
			switch (n->opratorid)
			{
			case 0:
				temp = !op1;
				break;
			case 10:
				temp = -op1;
				break;
			case 15:
				temp = sin(op1);
				break;
			case 16:
				temp = cos(op1);
				break;
			case 17:
				if (fabs(fmod(op1, PI) - PI2) < EPSILON)
					evalerr(4);
				else
					temp = tan(op1);
				break;
			case 18:
				temp = exp(op1);
				break;
			case 19:
				if (op1 >= 0.0)
					temp = log10(op1);
				else
					evalerr(5);
				break;
			case 20:
				if (op1 >= 0.0)
					temp = log(op1);
				else
					evalerr(6);
				break;
			case 21:
				if (op1 >= 0)
					temp = sqrt(op1);
				else
					evalerr(7);
				break;
			case 22:
				temp = step(op1);
				break;
			case 23:
				break;
			case 24:
				break;
			case 25:
				break;
			default:
				evalerr(8);
				break;
			} /* switch( n->opratorid ) */
			break;
		case NUM:
			if (n->opratorid == CONST)
			{
				temp = n->oprand;
			}
			else if (n->opratorid < num_var)
			{
				temp = VARIABLE[n->opratorid].val;
			}
			else
			{
				evalerr(9);
			}
			break;
		default:
			evalerr(n->type);
			break;
		}
	}
	return (temp);
}

/************************ error( char *s)  *******************************\

\*-----------------------------------------------------------------------*/

static void error(char *s)
{
	char *p;

	if (!ParseError)
	{

		ParseError = 1;

		strcpy(err1Message, Start_str);

		for (p = Start_str + 1; p < Str; p++)
			strcat(err2Message, "-");

		strcat(err2Message, "^");
		strcat(err2Message, s);
	}
}

/*************************** step( long double x)  *************************************\

\*-----------------------------------------------------------------------*/

static long double step(long double x)
{

	if (x < VARIABLE[0].val)
		return (1.0);
	else
		return (0.0);
}

/********************** match( char *token ) ****************************\

	Skips white space and advances Str to 1st non-white char. Then looks
	for token at the start of Str .

\*-----------------------------------------------------------------------*/

static int match(char *token)

{
	register char *p, *t;

	t = token; /* fast local copy of token */

	while (isspace(*Str) || (*Str == '\n') || (*Str == '\t'))
		Str++;

	for (p = Str; (*t) && (*t == *p); p++, t++)
		;

	return ((*t == '\0'));
}

/*************************** expr()  *************************************\

\*-----------------------------------------------------------------------*/

static PARSETREE expr(void)

{
	PARSETREE left, temp = NULL, term();

	temp = left = term();

	if (match("&&"))
	{
		advance(2);
		temp = binOpNode(1, left, expr());
	}
	else if (match("||"))
	{
		advance(2);
		temp = binOpNode(2, left, expr());
	}

	return (temp);
}

/*************************** term()  *************************************\
\*-----------------------------------------------------------------------*/

static PARSETREE term(void)

{
	PARSETREE left, temp = NULL, fact();

	temp = left = fact();

	if (match("<="))
	{
		advance(2);
		temp = binOpNode(3, left, term());
	}

	else if (match("<"))
	{
		advance(1);
		temp = binOpNode(4, left, term());
	}

	else if (match(">="))
	{
		advance(2);
		temp = binOpNode(5, left, term());
	}
	else if (match(">"))
	{
		advance(1);
		temp = binOpNode(6, left, term());
	}
	else if (match("=="))
	{
		advance(2);
		temp = binOpNode(7, left, term());
	}
	else if (match("!="))
	{
		advance(2);
		temp = binOpNode(8, left, term());
	}

	return (temp);
}

/*************************** fact()  *************************************\
\*-----------------------------------------------------------------------*/

static PARSETREE fact(void)

{
	PARSETREE left, temp = NULL, part();

	temp = left = part();

	if (match("+"))
	{
		advance(1);
		temp = binOpNode(9, left, fact());
	}
	else if (match("-"))
	{
		advance(1);
		temp = binOpNode(10, left, fact());
	}

	return (temp);
}

/*************************** part()  *************************************\
\*-----------------------------------------------------------------------*/

static PARSETREE part(void)

{
	PARSETREE left, temp = NULL, part2();

	temp = left = part2();

	if (match("*"))
	{
		advance(1);
		temp = binOpNode(11, left, part());
	}
	else if (match("%"))
	{
		advance(1);
		temp = binOpNode(12, left, part());
	}
	else if (match("/"))
	{

		/*---------------------------------------------------------------
			This code makes sure that division is done left to right.
			i.e. 2/3/2 = (2/3)/2 = .333333
		 ---------------------------------------------------------------*/

		while (match("/"))
		{
			advance(1);
			left = binOpNode(13, left, part2());
		}

		if (*Str == '*')
		{
			advance(1);
			temp = binOpNode(11, left, part());
		}
		else if (*Str == '%')
		{
			advance(1);
			temp = binOpNode(12, left, part());
		}
		else
			temp = left;
	}

	return (temp);
}

/*************************** part2()  *************************************\
\*-----------------------------------------------------------------------*/

static PARSETREE part2(void)

{
	PARSETREE left = NULL, get_constant();
	PARSETREE temp = NULL;
	// double pow() ;

	temp = left = get_constant();

	if (match("^"))
	{
		advance(1);
		temp = binOpNode(14, left, part2());
	}

	return (temp);
}
/*************************** myAtof()  ***********************************\
\*-----------------------------------------------------------------------*/

static long double myAtof(void)

{
	long double val = 0.0, power = 1.0, temp = 1.0, ex = 0;
	int i, sign = 1, sn = 1;

	while (*Str == ' ' || *Str == '\n' || *Str == '\t')
		Str++;

	for (;;)
	{
		if (match("+"))
		{
			advance(1);
		}
		else if (match("-"))
		{
			advance(1);
			sign *= -1;
		}
		else
			break;
	}

	while (*Str == ' ' || *Str == '\n' || *Str == '\t')
		Str++;

	if ((*Str < '0' || *Str > '9') && *Str != '.')
		error(" unexpected symbol ");

	for (val = 0; (*Str >= '0') && (*Str <= '9'); Str++)
		val = 10.0 * val + (*Str - '0');

	if (*Str == '.')
	{
		Str++;

		for (power = 1; (*Str >= '0') && (*Str <= '9'); Str++)
		{
			val = 10.0 * val + (*Str - '0');
			power *= 10;
		}
	}

	while (*Str == ' ' || *Str == '\n' || *Str == '\t')
		Str++;

	temp = 1;

	if (*Str == 'e' || *Str == 'E')
	{

		Str++;

		while (*Str == ' ' || *Str == '\n' || *Str == '\t')
			Str++;

		for (;;)
		{
			if (match("+"))
			{
				advance(1);
			}
			else if (match("-"))
			{
				advance(1);
				sn *= -1;
			}
			else
				break;
		}

		while (*Str == ' ' || *Str == '\n' || *Str == '\t')
			Str++;

		if (*Str < '0' || *Str > '9')
			error(" unexpected symbol ");

		for (ex = 0; (*Str >= '0') && (*Str <= '9'); Str++)
			ex = 10.0 * ex + (*Str - '0');

		temp = pow((long double)10.0, (long double)ex * (long double)sn);
	}

	return (sign * val * temp / power);
}

/*************************** get_constant()  ************************************\
\*-----------------------------------------------------------------------*/
static PARSETREE get_constant(void)

{
	PARSETREE temp = NULL, func();

	if (match("+"))
	{
		advance(1);
		temp = get_constant();
	}
	else if (match("-"))
	{
		advance(1);
		temp = unarOpNode(10, get_constant());
	}
	else if (match("!"))
	{
		advance(1);
		temp = unarOpNode(0, get_constant());
	}
	else
	{
		temp = func();
	}

	return (temp);
}

/*************************** func()  ************************************\
\*-----------------------------------------------------------------------*/

static PARSETREE func(void)

{
	PARSETREE temp = NULL;
	long double rval = 0.0;

	if (match("("))
	{
		/* get expression */
		advance(1);
		temp = expr();

		if (match(")"))
		{
			advance(1);
		}
		else
		{
			error(" Mis-matched parenthesis ");
			return (NULL);
		}
	}
	else if ((*Str >= 'a' && *Str <= 'z'))
	{

		int i;
		char *n;

		/*--------------------------
			Check for a function
		---------------------------*/

		for (i = FUNCSTART; i < NUMRATOR; i++)
		{
			n = OPRATOR[i];
			if (match(n) &&
				((*(Str + strlen(n)) < 'a') || (*(Str + strlen(n)) > 'z')))
				break;
		}

		if (i < NUMRATOR)
		{

			advance(strlen(n));

			if (!match("("))
			{
				error(" Missing parenthesis ");
				return (NULL);
			}

			advance(1);

			temp = unarOpNode(i, expr());

			if (match(")"))
				advance(1);
			else
			{
				error(" Mis-matched parenthesis ");
				return (NULL);
			}
		}
		else
		{
			/*----------------------------
				Check for a variable .
			-----------------------------*/

			for (i = 0; i < num_var; i++)
			{
				n = VARIABLE[i].name;
				if (match(n) &&
					((*(Str + strlen(n)) < 'a') || (*(Str + strlen(n)) > 'z')))
					break;
			}

			if (i < num_var)
			{
				advance(strlen(n));
				temp = numNode(i, 0.0);
				if (temp == NULL)
				{
					error(" Out of memory");
					return (NULL);
				}
			}
			n = NULL;
		}
	}
	else
	{ /* or, get number */
		rval = myAtof();
		temp = numNode(CONST, rval);
	}

	if (temp == NULL)
	{
		error(" unexpected symbol ");
		return (NULL);
	}

	return (temp);
}

/*************************** parse()  ************************************\
\*-----------------------------------------------------------------------*/

void *parse(char *expr_p[], int *err, char err_mess[])
{
	PARSETREE rval;

	Start_str = Str = *expr_p;

	/*---------------------------------
		Skip leading white space.
		This was added on Jan 28,'89.
	----------------------------------*/
	while (*Str == ' ' || *Str == '\t')
	{
		Str++;
	}

	if (!Str || !*Str)
	{
		*err = -1;
		strcpy(err_mess, *expr_p);
		strcat(err_mess, "\n Not a Function ");
		rval = NULL;
	}
	else
	{
		ParseError = 0;
		err1Message[0] = '\0';
		err2Message[0] = '\0';

		/*----------------------------------------------------------
			expr() actually starts the recursive decent parser
		-----------------------------------------------------------*/
		rval = expr();

		/*---------------------------------------------------------
			This code checks for incomplete evaluation of the
			expression.  The parser can be fooled into evaluating
			the first part of an expression and then thinking that
			it is done.  This can only happen with illegal
			expressions.
		---------------------------------------------------------*/
		while (*Str != '\0')
		{
			if (*Str != ' ' && *Str != '\n' && *Str != '\t')
			{
				error(" unexpected symbol ");
				break;
			}
			Str++;
		}

		*err = ParseError;

		if (ParseError)
		{
			strcpy(err_mess, err1Message);
			strcat(err_mess, "\n  ");
			strcat(err_mess, err2Message);
			disposParseTree(rval);
			rval = NULL;
		}
		else
		{
			err_mess[0] = '\0';
		}

		/*------------------------------------------------------
			This line of code incremented our pointer to the
			end of the parsed string, it is not really a good
			side effect, so it was removed. Jan 28, '89.
		*expr_p = Str ;
		--------------------------------------------------------*/
	}
	return ((void *)rval);
}

/*************************** main()  *************************************\
\*-----------------------------------------------------------------------*/

#if MAIN

int main(void)

{

	int e_err = 0, p_err = 0;
	char buf[255], *p, p_err_mess[80];
	PARSETREE tree = NULL;
	long double temp = 0.0;
	char prompt[254] = "\nEnter an expression, or return to quit >";

	printf("%s", prompt);

	// for ( ; gets( buf ); printf(">") ) {
	for (; fgets(buf, 254, stdin); printf("%s", prompt))
	{

		p = buf;

		// 	if ( !*buf )
		// if ( p == "" || p == "\n")
		// 	break ;
		if (strcmp(p, "") == 0 || strcmp(p, "\n") == 0)
			break;

		disposParseTree(tree);
		tree = NULL;
		tree = parse(&p, &p_err, p_err_mess);
		temp = eval(tree, &e_err);
		printf(" ANS = %Lg \n", temp);
		printf(" %s \n ", p_err_mess);
		setVariable("t", temp);
		printf(" evaluation error 	#%d\n", e_err);
		printf(" parsing error 		#%d\n", p_err);
	}

	printf("\n Good bye! \n\n");
}
#endif