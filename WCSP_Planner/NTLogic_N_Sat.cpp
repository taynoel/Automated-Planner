//
//  NTLogic_N_Sat.cpp
//  WCSP_planner2
//
//  Created by Noel Tay on 2/6/16.
//  Copyright (c) 2016 Noel Tay. All rights reserved.
//

#include "NTLogic_N_Sat.h"
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#define NTDEF_MAXSTRSIZE 500
int NTL_ReturnValue(const char* Stri);
int NTL_Mode1_or(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int strn,Startn=0,Bracketn=0;
    int StrLength=(int)strlen(Stri);
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='o' && Stri[f+1]=='r'){Startn=f+2;break;}
    int Mode=0;//0=start 1=found bracket
    int anss=0;
    strn=0;str[0]='\0';
    for(int f=Startn;f<StrLength;f++)
    {
        if(Mode==0)
        {
            if(Stri[f]>='0' && Stri[f]<='9')
            {
                if(Stri[f]=='1')anss=1;
            }
            else if(Stri[f]=='(')
            {
                strn=0;str[strn]=Stri[f];str[strn+1]='\0';
                Mode=1;Bracketn=1;
            }
        }
        else if(Mode==1)
        {
            strn++;str[strn]=Stri[f];
            str[strn+1]='\0';
            if(Stri[f]=='(')Bracketn++;
            else if(Stri[f]==')')Bracketn--;
            if(Bracketn<=0){anss=NTL_ReturnValue(str);
                Mode=0;}
        }if(anss==1)break;
    }return anss;
}

int NTL_Mode2_and(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int strn,Startn=0,Bracketn=0;
    int StrLength=(int)strlen(Stri);
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='a' && Stri[f+1]=='n'){Startn=f+3;break;}
    int Mode=0;//0=start 1=found bracket
    int anss=1;
    strn=0;str[0]='\0';
    for(int f=Startn;f<StrLength;f++)
    {
        if(Mode==0)
        {
            if(Stri[f]>='0' && Stri[f]<='9')
            {
                if(Stri[f]=='0')anss=0;
            }
            else if(Stri[f]=='(')
            {
                strn=0;str[strn]=Stri[f];str[strn+1]='\0';
                Mode=1;Bracketn=1;
            }
        }
        else if(Mode==1)
        {
            strn++;str[strn]=Stri[f];
            str[strn+1]='\0';
            if(Stri[f]=='(')Bracketn++;
            else if(Stri[f]==')')Bracketn--;
            if(Bracketn==0){anss=NTL_ReturnValue(str);
                Mode=0;}
        }if(anss==0)break;
    }return anss;
}

int NTL_Mode3_eq(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int strn,Startn=0,Bracketn=0;
    int StrLength=(int)strlen(Stri);
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='='){Startn=f+1;break;}
    int Mode=0;//0=start 1=found bracket 2=found number
    int ArgMod=0;//1 1st arg obtained 2 2nd arg obtained
    int arg1=0,arg2=0;
    strn=0;str[0]='\0';
    for(int f=Startn;f<StrLength;f++)
    {
        if(Mode==0)
        {
            strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            if(Stri[f]>='0' && Stri[f]<='9')Mode=2;
            else if(Stri[f]=='('){Mode=1;Bracketn=1;}
        }
        else if(Mode==1)
        {
            strn++;str[strn]=Stri[f];
            str[strn+1]='\0';
            if(Stri[f]=='(')Bracketn++;
            else if(Stri[f]==')')Bracketn--;
            if(Bracketn==0){
                if(ArgMod==0)arg1=NTL_ReturnValue(str);
                else if(ArgMod==1)arg2=NTL_ReturnValue(str);
                ArgMod++;
                Mode=0;}
        }
        else if(Mode==2)
        {
            if(Stri[f]>='0' && Stri[f]<='9')
            {
                strn++;str[strn]=Stri[f];
                str[strn+1]='\0';
            }
            else if(Stri[f]==' ' || Stri[f]==')')
            {
                Mode=0;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
            }
            else if(Stri[f]=='(')
            {
                Mode=1;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
                strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            }
        }if(ArgMod==2)break;
    }return (arg1 == arg2);
}

int NTL_Mode4_imp(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int strn,Startn=0,Bracketn=0;
    int StrLength=(int)strlen(Stri);
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='='){Startn=f+2;break;}
    int Mode=0;//0=start 1=found bracket 2=found number
    int ArgMod=0;//1 1st arg obtained 2 2nd arg obtained
    int arg1=0,arg2=0;
    strn=0;str[0]='\0';
    for(int f=Startn;f<StrLength;f++)
    {
        if(Mode==0)
        {
            strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            if(Stri[f]>='0' && Stri[f]<='9')Mode=2;
            else if(Stri[f]=='('){Mode=1;Bracketn=1;}
        }
        else if(Mode==1)
        {
            strn++;str[strn]=Stri[f];
            str[strn+1]='\0';
            if(Stri[f]=='(')Bracketn++;
            else if(Stri[f]==')')Bracketn--;
            if(Bracketn==0)
            {
                if(ArgMod==0)arg1=NTL_ReturnValue(str);
                else if(ArgMod==1)arg2=NTL_ReturnValue(str);
                ArgMod++;
            
                Mode=0;}
        }
        else if(Mode==2)
        {
            if(Stri[f]>='0' && Stri[f]<='9')
            {
                strn++;str[strn]=Stri[f];
                str[strn+1]='\0';
            }
            else if(Stri[f]==' ' || Stri[f]==')')
            {
                Mode=0;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
            }
            else if(Stri[f]=='(')
            {
                Mode=1;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
                strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            }
        }if(ArgMod==2)break;
    }
    int ReturnAns=0;
    if(arg1==0)ReturnAns=1;
    else if(arg1==1 && arg2==1)ReturnAns=1;
    else if(arg1==1 && arg2==0)ReturnAns=0;
    if(arg1>1 || arg1<0 || arg2>1 || arg2<0 ){printf("Syntax Error 2\n");exit(2);}
    return ReturnAns;
}

int NTL_Mode5_leq(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int strn,Startn=0,Bracketn=0;
    int StrLength=(int)strlen(Stri);
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='>'){Startn=f+2;break;}
    int Mode=0;//0=start 1=found bracket 2=found number
    int ArgMod=0;//1 1st arg obtained 2 2nd arg obtained
    int arg1=0,arg2=0;
    strn=0;str[0]='\0';
    for(int f=Startn;f<StrLength;f++)
    {
        if(Mode==0)
        {
            strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            if(Stri[f]>='0' && Stri[f]<='9')Mode=2;
            else if(Stri[f]=='('){Mode=1;Bracketn=1;}
        }
        else if(Mode==1)
        {
            strn++;str[strn]=Stri[f];
            str[strn+1]='\0';
            if(Stri[f]=='(')Bracketn++;
            else if(Stri[f]==')')Bracketn--;
            if(Bracketn==0){
                if(ArgMod==0)arg1=NTL_ReturnValue(str);
                else if(ArgMod==1)arg2=NTL_ReturnValue(str);
                ArgMod++;
                Mode=0;}
        }
        else if(Mode==2)
        {
            if(Stri[f]>='0' && Stri[f]<='9')
            {
                strn++;str[strn]=Stri[f];
                str[strn+1]='\0';
            }
            else if(Stri[f]==' ' || Stri[f]==')')
            {
                Mode=0;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
            }
            else if(Stri[f]=='(')
            {
                Mode=1;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
                strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            }
        }if(ArgMod==2)break;
    }return (arg1 >= arg2);
}

int NTL_Mode6_lt(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int strn,Startn=0,Bracketn=0;
    int StrLength=(int)strlen(Stri);
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='>'){Startn=f+1;break;}
    int Mode=0;//0=start 1=found bracket 2=found number
    int ArgMod=0;//1 1st arg obtained 2 2nd arg obtained
    int arg1=0,arg2=0;
    strn=0;str[0]='\0';
    for(int f=Startn;f<StrLength;f++)
    {
        if(Mode==0)
        {
            strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            if(Stri[f]>='0' && Stri[f]<='9')Mode=2;
            else if(Stri[f]=='('){Mode=1;Bracketn=1;}
        }
        else if(Mode==1)
        {
            strn++;str[strn]=Stri[f];
            str[strn+1]='\0';
            if(Stri[f]=='(')Bracketn++;
            else if(Stri[f]==')')Bracketn--;
            if(Bracketn==0){
                if(ArgMod==0)arg1=NTL_ReturnValue(str);
                else if(ArgMod==1)arg2=NTL_ReturnValue(str);
                ArgMod++;
                Mode=0;}
        }
        else if(Mode==2)
        {
            if(Stri[f]>='0' && Stri[f]<='9')
            {
                strn++;str[strn]=Stri[f];
                str[strn+1]='\0';
            }
            else if(Stri[f]==' ' || Stri[f]==')')
            {
                Mode=0;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
            }
            else if(Stri[f]=='(')
            {
                Mode=1;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
                strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            }
        }if(ArgMod==2)break;
    }return (arg1 > arg2);
}


int NTL_Mode7_seq(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int strn,Startn=0,Bracketn=0;
    int StrLength=(int)strlen(Stri);
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='<'){Startn=f+2;break;}
    int Mode=0;//0=start 1=found bracket 2=found number
    int ArgMod=0;//1 1st arg obtained 2 2nd arg obtained
    int arg1=0,arg2=0;
    strn=0;str[0]='\0';
    for(int f=Startn;f<StrLength;f++)
    {
        if(Mode==0)
        {
            strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            if(Stri[f]>='0' && Stri[f]<='9')Mode=2;
            else if(Stri[f]=='('){Mode=1;Bracketn=1;}
        }
        else if(Mode==1)
        {
            strn++;str[strn]=Stri[f];
            str[strn+1]='\0';
            if(Stri[f]=='(')Bracketn++;
            else if(Stri[f]==')')Bracketn--;
            if(Bracketn==0){
                if(ArgMod==0)arg1=NTL_ReturnValue(str);
                else if(ArgMod==1)arg2=NTL_ReturnValue(str);
                ArgMod++;
                Mode=0;}
        }
        else if(Mode==2)
        {
            if(Stri[f]>='0' && Stri[f]<='9')
            {
                strn++;str[strn]=Stri[f];
                str[strn+1]='\0';
            }
            else if(Stri[f]==' ' || Stri[f]==')')
            {
                Mode=0;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
            }
            else if(Stri[f]=='(')
            {
                Mode=1;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
                strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            }
        }if(ArgMod==2)break;
    }return (arg1 <= arg2);
}

int NTL_Mode8_st(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int strn,Startn=0,Bracketn=0;
    int StrLength=(int)strlen(Stri);
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='<'){Startn=f+1;break;}
    int Mode=0;//0=start 1=found bracket 2=found number
    int ArgMod=0;//1 1st arg obtained 2 2nd arg obtained
    int arg1=0,arg2=0;
    strn=0;str[0]='\0';
    for(int f=Startn;f<StrLength;f++)
    {
        if(Mode==0)
        {
            strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            if(Stri[f]>='0' && Stri[f]<='9')Mode=2;
            else if(Stri[f]=='('){Mode=1;Bracketn=1;}
        }
        else if(Mode==1)
        {
            strn++;str[strn]=Stri[f];
            str[strn+1]='\0';
            if(Stri[f]=='(')Bracketn++;
            else if(Stri[f]==')')Bracketn--;
            if(Bracketn==0){
                if(ArgMod==0)arg1=NTL_ReturnValue(str);
                else if(ArgMod==1)arg2=NTL_ReturnValue(str);
                ArgMod++;
                Mode=0;}
        }
        else if(Mode==2)
        {
            if(Stri[f]>='0' && Stri[f]<='9')
            {
                strn++;str[strn]=Stri[f];
                str[strn+1]='\0';
            }
            else if(Stri[f]==' ' || Stri[f]==')')
            {
                Mode=0;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
            }
            else if(Stri[f]=='(')
            {
                Mode=1;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
                strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            }
        }if(ArgMod==2)break;
    }return (arg1 < arg2);
}

int NTL_Mode9_not(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int strn,Startn=0,Bracketn=0;
    int StrLength=(int)strlen(Stri);
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='n'){Startn=f+3;break;}
    int Mode=0;//0=start 1=found bracket 2=found number
    int ArgMod=0;//1 1st arg obtained 2 2nd arg obtained
    int arg1=0,arg2=0;
    strn=0;str[0]='\0';
    for(int f=Startn;f<StrLength;f++)
    {
        if(Mode==0)
        {
            strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            if(Stri[f]>='0' && Stri[f]<='9')Mode=2;
            else if(Stri[f]=='('){Mode=1;Bracketn=1;}
        }
        else if(Mode==1)
        {
            strn++;str[strn]=Stri[f];
            str[strn+1]='\0';
            if(Stri[f]=='(')Bracketn++;
            else if(Stri[f]==')')Bracketn--;
            if(Bracketn==0){
                if(ArgMod==0)arg1=NTL_ReturnValue(str);
                else if(ArgMod==1)arg2=NTL_ReturnValue(str);
                ArgMod++;
                Mode=0;}
        }
        else if(Mode==2)
        {
            if(Stri[f]>='0' && Stri[f]<='9')
            {
                strn++;str[strn]=Stri[f];
                str[strn+1]='\0';
            }
            else if(Stri[f]==' ' || Stri[f]==')')
            {
                Mode=0;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
            }
            else if(Stri[f]=='(')
            {
                Mode=1;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
                strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            }
        }if(ArgMod==1)break;
    }return (!(arg1));
}


int NTL_Mode10_neq(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int strn,Startn=0,Bracketn=0;
    int StrLength=(int)strlen(Stri);
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='n'){Startn=f+3;break;}
    int Mode=0;//0=start 1=found bracket 2=found number
    int ArgMod=0;//1 1st arg obtained 2 2nd arg obtained
    int arg1=0,arg2=0;
    strn=0;str[0]='\0';
    for(int f=Startn;f<StrLength;f++)
    {
        if(Mode==0)
        {
            strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            if(Stri[f]>='0' && Stri[f]<='9')Mode=2;
            else if(Stri[f]=='('){Mode=1;Bracketn=1;}
        }
        else if(Mode==1)
        {
            strn++;str[strn]=Stri[f];
            str[strn+1]='\0';
            if(Stri[f]=='(')Bracketn++;
            else if(Stri[f]==')')Bracketn--;
            if(Bracketn==0){
                if(ArgMod==0)arg1=NTL_ReturnValue(str);
                else if(ArgMod==1)arg2=NTL_ReturnValue(str);
                ArgMod++;
                Mode=0;}
        }
        else if(Mode==2)
        {
            if(Stri[f]>='0' && Stri[f]<='9')
            {
                strn++;str[strn]=Stri[f];
                str[strn+1]='\0';
            }
            else if(Stri[f]==' ' || Stri[f]==')')
            {
                Mode=0;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
            }
            else if(Stri[f]=='(')
            {
                Mode=1;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
                strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            }
        }if(ArgMod==2)break;
    }return (arg1 != arg2);
}

int NTL_Mode11_add(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int strn,Startn=0,Bracketn=0;
    int StrLength=(int)strlen(Stri);
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='+'){Startn=f+1;break;}
    int Mode=0;//0=start 1=found bracket 2=found number
    int ArgMod=0;//1 1st arg obtained 2 2nd arg obtained
    int arg1=0,arg2=0;
    strn=0;str[0]='\0';
    for(int f=Startn;f<StrLength;f++)
    {
        if(Mode==0)
        {
            strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            if(Stri[f]>='0' && Stri[f]<='9')Mode=2;
            else if(Stri[f]=='('){Mode=1;Bracketn=1;}
        }
        else if(Mode==1)
        {
            strn++;str[strn]=Stri[f];
            str[strn+1]='\0';
            if(Stri[f]=='(')Bracketn++;
            else if(Stri[f]==')')Bracketn--;
            if(Bracketn==0){
                if(ArgMod==0)arg1=NTL_ReturnValue(str);
                else if(ArgMod==1)arg2=NTL_ReturnValue(str);
                ArgMod++;
                Mode=0;}
        }
        else if(Mode==2)
        {
            if(Stri[f]>='0' && Stri[f]<='9')
            {
                strn++;str[strn]=Stri[f];
                str[strn+1]='\0';
            }
            else if(Stri[f]==' ' || Stri[f]==')')
            {
                Mode=0;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
            }
            else if(Stri[f]=='(')
            {
                Mode=1;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
                strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            }
        }if(ArgMod==2)break;
    }return (arg1 + arg2);
}

int NTL_Mode12_subt(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int strn,Startn=0,Bracketn=0;
    int StrLength=(int)strlen(Stri);
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='-'){Startn=f+1;break;}
    int Mode=0;//0=start 1=found bracket 2=found number
    int ArgMod=0;//1 1st arg obtained 2 2nd arg obtained
    int arg1=0,arg2=0;
    strn=0;str[0]='\0';
    for(int f=Startn;f<StrLength;f++)
    {
        if(Mode==0)
        {
            strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            if(Stri[f]>='0' && Stri[f]<='9')Mode=2;
            else if(Stri[f]=='('){Mode=1;Bracketn=1;}
        }
        else if(Mode==1)
        {
            strn++;str[strn]=Stri[f];
            str[strn+1]='\0';
            if(Stri[f]=='(')Bracketn++;
            else if(Stri[f]==')')Bracketn--;
            if(Bracketn==0){
                if(ArgMod==0)arg1=NTL_ReturnValue(str);
                else if(ArgMod==1)arg2=NTL_ReturnValue(str);
                ArgMod++;
                Mode=0;}
        }
        else if(Mode==2)
        {
            if(Stri[f]>='0' && Stri[f]<='9')
            {
                strn++;str[strn]=Stri[f];
                str[strn+1]='\0';
            }
            else if(Stri[f]==' ' || Stri[f]==')')
            {
                Mode=0;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
            }
            else if(Stri[f]=='(')
            {
                Mode=1;
                if(ArgMod==0)arg1=atoi(str);
                else if(ArgMod==1)arg2=atoi(str);
                ArgMod++;
                strn=0;str[strn]=Stri[f];str[strn+1]='\0';
            }
        }if(ArgMod==2)break;
    }return (arg1 - arg2);
}

int NTL_Mode0_gnd(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int StrLength=(int)strlen(Stri);
    int Startn_=0;
    int Startn=0,Bracketn=0;
    bool startFlag=0;
    //cancel front part
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='('){Startn_=f+1;break;}
    for(int f=Startn_;f<StrLength;f++)
        if(Stri[f]=='('){Startn=f;break;}
    int strn=1;
    str[0]='(';Bracketn=1;
    while (Bracketn!=0 || startFlag==0)
    {
        startFlag=1;
        int v=Startn+strn;
        str[strn]=Stri[v];str[strn+1]='\0';
        if(Stri[v]=='(')Bracketn++;
        else if(Stri[v]==')')Bracketn--;
        strn++;
    }
    return NTL_ReturnValue(str);
}

int NTL_Mode13_valgnd(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    int StrLength=(int)strlen(Stri);
    int Startn=0;
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='('){Startn=f+1;break;}
    int strn=0;
    bool StartNumberFlag=0;
    for(int f=Startn;f<StrLength;f++)
    {
    
        if(Stri[f]>='0' && Stri[f]<='9')
        {
            StartNumberFlag=1;
            str[strn]=Stri[f];str[strn+1]='\0';
            strn++;
        }
        else
        {
            if(StartNumberFlag==1)break;
        }
    }
    
    
    return atoi(str);
}





int NTL_ReturnValue(const char* Stri)
{
    //printf("%s\n",Stri);
    int StrLength=(int)strlen(Stri);
    int Mode=-1;
    int Startn=0;
    int Anss=0;
    for(int f=0;f<StrLength;f++)
        if(Stri[f]=='(' ){Startn=f+1;break;}
    for(int f=Startn;f<StrLength;f++)
    {
        if(Stri[f]=='o') Mode=1;     //1 or
        else if (Stri[f]=='a')Mode=2;//2 and
        else if (Stri[f]=='=')
        {
            if(Stri[f+1]!='>') Mode=3;//3 = double
            else Mode=4;             //4 =>
        }
        else if(Stri[f]=='>')
        {
            if(Stri[f+1]=='=')Mode=5;//5 >=
            else Mode=6;             //6 >
        }
        else if (Stri[f]=='<')
        {
            if(Stri[f+1]=='=')Mode=7;//7 <=
            else Mode=8;             //8 <
        }
        else if(Stri[f]=='n')
        {
            if(Stri[f+1]=='o')Mode=9;//9 not
            else Mode=10;//10 neq double
        }
        else if(Stri[f]=='+')Mode=11;//11 +
        else if(Stri[f]=='-')Mode=12;//12 -
        else if(Stri[f]=='(' )Mode=0;//Ground
        else if(Stri[f]>='0' && Stri[f]<='9')Mode=13;//value ground
        else if(Stri[f]!=' '){printf("Syntax ERROR1\n");exit(1);}
        
        
        if(Mode!=-1)break;
    }
    if(Mode==1){Anss=NTL_Mode1_or(Stri);}
    else if(Mode==2){Anss=NTL_Mode2_and(Stri);}
    else if(Mode==3){Anss=NTL_Mode3_eq(Stri);}
    else if(Mode==4){Anss=NTL_Mode4_imp(Stri);}
    else if(Mode==5){Anss=NTL_Mode5_leq(Stri);}
    else if(Mode==6){Anss=NTL_Mode6_lt(Stri);}
    else if(Mode==7){Anss=NTL_Mode7_seq(Stri);}
    else if(Mode==8){Anss=NTL_Mode8_st(Stri);}
    else if(Mode==9){Anss=NTL_Mode9_not(Stri);}
    else if(Mode==10){Anss=NTL_Mode10_neq(Stri);}
    else if(Mode==11){Anss=NTL_Mode11_add(Stri);}
    else if(Mode==12){Anss=NTL_Mode12_subt(Stri);}
    else if(Mode==0){Anss=NTL_Mode0_gnd(Stri);}
    else if(Mode==13){Anss=NTL_Mode13_valgnd(Stri);}
    
    return Anss;
}


void NTL_Prep(const char* Stri,char str[NTDEF_MAXSTRSIZE])
{
    int StrLength=(int)strlen(Stri);
    int n=0,nStri=0;
    while(n<=StrLength)
    {
        if(Stri[nStri]=='t' && Stri[nStri+1]=='r')
        {
            str[n]='1';nStri+=4;n++;
        }
        else if(Stri[nStri]=='f')
        {
            str[n]='0';nStri+=5;n++;
        }
        else
        {
            str[n]=Stri[nStri];nStri+=1;n++;
        }
    }
}

int NTL_GetValue(const char* Stri)
{
    char str[NTDEF_MAXSTRSIZE];
    NTL_Prep(Stri, str);
    int Result=NTL_ReturnValue(str);
    return Result;
}
