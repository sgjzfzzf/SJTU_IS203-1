#include <stdio.h>
#include <malloc.h>
#include <string.h>
#define ISCHAR(ch) (ch != ' ' && ch != '\t' && ch != '\n' && ch != '\r')

int read_words(FILE *fin, int charsNumber)
{
    char *str = (char *)malloc(sizeof(char) * charsNumber + 1);
    fread(str, charsNumber + 1, 1, fin);
    int wordsNumber = 0, isLastSpace = 1;
    for (int i = 0; i < charsNumber; ++i)
    {
        if (!ISCHAR(str[i]))
        {
            isLastSpace = 1;
        }
        else if (isLastSpace == 1)
        {
            ++wordsNumber;
            isLastSpace = 0;
        }
    }
    free(str);
    fclose(fin);
    return wordsNumber;
}