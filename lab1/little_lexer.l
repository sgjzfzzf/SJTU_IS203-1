%{
    #include <stdio.h>
    #include "read_words.c"
    int lineNumber = 0, wordsNumber, charsNumber = 0;
%}

NAME        ^#\ ([0-9a-zA-Z]+\.sealpp)
COMMENT     #([\ \t]|.)*
SPACE       [\ \t\r\n]+
TYPEID      Int|Float|String|Bool|Void
KEYWORD     fprintf|while|aafor|if|else|continue|break|return
SYMBOL      \<\=|\>\=|\=\=|\:\=|\%f|\%s|\%lld|\|\||\&\&|\%|\~|\^|\-|\*|\/|\+|\-|\;|\=|\:|\||\&|\{|\}|\(|\)|\\|\<|\>
CONST       [0-9]+\.[0-9]+|0|[1-9][0-9]*
FUNCTION    func\ {OBJECTED}
STDOUT      stdout|stderr
OBJECTED    [a-z][a-zA-Z0-9]*
OTHERS      .

%%

{NAME}      {
                charsNumber += yyleng;
                printf("#name %s\n", yytext+2);
            }
{COMMENT}   {
                charsNumber += yyleng;
                
            }
{SPACE}     {
                charsNumber += yyleng;
                for (int i = 0; i < yyleng; ++i)
                {
                    if (yytext[i] == '\n')
                    {
                        ++lineNumber;
                    }
                }
            }
{TYPEID}    {
                charsNumber += yyleng;
                printf("#%d TYPEID %s\n", lineNumber, yytext);
            }
{KEYWORD}   {
                charsNumber += yyleng;
                printf("#%d KEYWORD %s\n", lineNumber, yytext);
            }
{SYMBOL}    {
                charsNumber += yyleng;
                printf("#%d %s\n", lineNumber, yytext);
            }
{CONST}     {
                charsNumber += yyleng;
                printf("#%d CONST %s\n", lineNumber, yytext);
            }
{FUNCTION}  {
                charsNumber += yyleng;
                printf("#%d %s\n", lineNumber, yytext);
            }
{STDOUT}    {
                charsNumber += yyleng;
            }
{OBJECTED}  {
                charsNumber += yyleng;
                printf("#%d OBJECTED %s\n", lineNumber, yytext);
            }
{OTHERS}    {
                charsNumber += yyleng;
            }

%%

int main(int argc, char *argv[])
{
    yylex();
    fseek(yyin, 0, SEEK_SET);
    wordsNumber = read_words(yyin, charsNumber);
    printf("lines:%d,words:%d,chars:%d\n", lineNumber, wordsNumber, charsNumber);
    return 0;
}

int yywrap()
{
    return 1;
}
