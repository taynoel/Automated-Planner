//
//  NTfunc.cpp
//  WCSP_planner1
//
//  Created by Noel Tay on 1/22/16.
//  Copyright (c) 2016 Noel Tay. All rights reserved.
//

#include "NTfunc.h"
#include "define.h"

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <string.h>
#include "NTLogic_N_Sat.h"

NTSTRCT_ACTIVITY* ACTIVITY_LIST;
NTSTRCT_VARIABLE* VARIABLE_LIST;
NTSTRCT_ACTYREV* REVACTVTY_LIST;
NTSTRCT_GOAL* GOAL_LIST;
int** LOCALINVALID2OPT;

int NUM_ACTIVITY,NUM_VARIABLE,NUM_REVACTIVITY,NUM_GOAL,NUM_INVALIDLOCAL;
int FinalUB=1000000;
bool STOPFLAG;
FILE* FH;

char* NTf_readWholeTextFile(const char* FileName, long* BufferSize);
int NTf_CountNumSectionwDelimitor(const char* buffer, const char* delimiter);
int NTCheck_Get_Val_VariableList(const char* Name,int *Value,char* Sort,char* Type );
int NTf_getSOmeVariableNoOneUse(const char* STR);
int NTf_SATtest(const char* STR);
int NTMEMETIC(int NA,int TS,int CS, int State[],int** Local2opt,int ArraySize );
int NTLBCost_discreteActivity(int Act[NTDEF_NUMSEQUENCE-1],int initState[]);
int Jmemetic(int NumberOfActivities, int TotalSequence, int CurrentSequence, int S[], intMATRIX LUT, int size);

char* NTf_readWholeTextFile(const char* FileName, long* BufferSize)
{
    char *buffer;
    long test;
    FILE *fh = fopen(FileName, "rb");
    if ( fh != NULL )
    {
        fseek(fh, 0L, SEEK_END);
        *BufferSize = ftell(fh);
        rewind(fh);
        buffer = (char*)malloc(sizeof(char)*(*BufferSize+1));
        if ( buffer != NULL )
        {
            test=fread(buffer, *BufferSize, 1, fh);
            fclose(fh); fh = NULL;
        }
        if (fh != NULL) fclose(fh);
    }
    buffer[*BufferSize]='\0';
    return buffer;
}

int NT_cmpfunc (const void * a, const void * b)
{return ( *(int*)a - *(int*)b );}

int NTf_CountNumSectionwDelimitor(const char* buffer, const char* delimiter)
{
    char* buffer2=(char*)malloc(sizeof(char)*(strlen(buffer)+1));
    char* PCH;
    strcpy(buffer2, buffer);
    PCH=strtok(buffer2, delimiter);
    int n=0;
    while( PCH!=NULL)
    {
        char* ptr1=strstr(PCH, "//");
        if(ptr1!=NULL)break;
        n++;
        PCH=strtok(NULL, delimiter);
    }
    free(buffer2);
    return n;
}

void Ticc(char a)
{
    static clock_t T1,T2;
    if(a=='i')
        T1=clock();
    else
    {
        T2=clock();
        float Tdiff=(((float)T2 - (float)T1) / CLOCKS_PER_SEC );
        printf("||||||||||  Time = %f\n",Tdiff);
    }
}

float NTN_Ticc()
{
    static clock_t T1,T2;
    static bool flag=0;
    float Tdiff;
    if(flag==0)
    {
        T1=clock();
        flag=1;
        return 0;
    }
    else
    {
        T2=clock();
        Tdiff=(((float)T2 - (float)T1) / CLOCKS_PER_SEC );
        return Tdiff;
    }
}


void NT_genLocalInconsistencyforMemetic()
{
    NUM_INVALIDLOCAL=0;
    char strformula1[NTDEF_MAXSTRSIZE];
    char strformula2[NTDEF_MAXSTRSIZE];
    char strTotal[NTDEF_MAXSTRSIZE];
    char strVarDec[NTDEF_MAXSTRSIZE];
    char *PCH;
    int* VariableFlag=(int*)malloc(sizeof(int)*NUM_VARIABLE);//#release
    if(LOCALINVALID2OPT==NULL)LOCALINVALID2OPT=(int**)malloc(sizeof(int)*2);//#global var
    for(int f=0;f<NUM_ACTIVITY;f++)
    {
        //sprintf(str,"(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse (and ");
        strcpy(strformula1, ":formula(and ");
        for(int ff=0;ff<ACTIVITY_LIST[f].effect_num;ff++)
        {
            strcat(strformula1, "(= ");
            strcat(strformula1, ACTIVITY_LIST[f].effect_var[ff].s);strcat(strformula1, " ");
            strcat(strformula1, ACTIVITY_LIST[f].effect[ff].s);strcat(strformula1, " )");
        }strcat(strformula1, ")");//done with 1st formula
        
        
        for(int f2=0;f2<NUM_ACTIVITY;f2++)
        {
            strcpy(strformula2, ":formula(and ");
            for(int ff=0;ff<ACTIVITY_LIST[f2].effect_num;ff++)
            {
                strcat(strformula2, "(= ");
                strcat(strformula2, ACTIVITY_LIST[f2].effect_var[ff].s);strcat(strformula2, " ");
                strcat(strformula2, ACTIVITY_LIST[f2].effect[ff].s);strcat(strformula2, " )");
            }strcat(strformula2, ")");//done with 2nd formula
            
            strcpy(strVarDec, ":extrafuns( ");
            sprintf(strTotal, "%s %s",strformula1,strformula2);//temporary use strtotal
            PCH=strtok(strTotal, " ");
            for(int fff=0;fff<NUM_VARIABLE;fff++)
                VariableFlag[fff]=0;
            
            while (PCH!=NULL)
            {
                char strr1[NTDEF_MAXSTRSIZEm];
                char Sort,Type;int Val;
                int varindex=NTCheck_Get_Val_VariableList(PCH, &Val, &Sort, &Type);
                if(varindex!=-1)
                {
                    if(VariableFlag[varindex]==0)
                    {
                        VariableFlag[varindex]=1;
                        if(Sort=='i')
                            sprintf(strr1,"( %s Int)",VARIABLE_LIST[varindex].Variablename);
                        
                        else if(Sort=='b')
                            sprintf(strr1,"( %s Bool)",VARIABLE_LIST[varindex].Variablename);
                        else if(Sort=='I')
                            sprintf(strr1,"( %s Int)",VARIABLE_LIST[varindex].Variablename);
                        strcat(strVarDec, strr1);
                    }
                }PCH=strtok(NULL, " ");
            }strcat(strVarDec, ")"); //done with variable declaration
            
            sprintf(strTotal, "(benchmark tst %s %s %s )",strVarDec,strformula1,strformula2);
            
            
            //Start allocating and storing
            if(!NTf_SATtest(strTotal))
            {
                if(NUM_INVALIDLOCAL==0)
                {
                    NUM_INVALIDLOCAL++;
                    LOCALINVALID2OPT[0]=(int*)malloc(sizeof(int)*1);
                    LOCALINVALID2OPT[1]=(int*)malloc(sizeof(int)*1);
                    LOCALINVALID2OPT[0][NUM_INVALIDLOCAL-1]=f;
                    LOCALINVALID2OPT[1][NUM_INVALIDLOCAL-1]=f2;
                }
                else
                {
                    NUM_INVALIDLOCAL++;
                    LOCALINVALID2OPT[0]=(int*)realloc(LOCALINVALID2OPT[0], sizeof(int)*NUM_INVALIDLOCAL);
                    LOCALINVALID2OPT[1]=(int*)realloc(LOCALINVALID2OPT[1], sizeof(int)*NUM_INVALIDLOCAL);
                    LOCALINVALID2OPT[0][NUM_INVALIDLOCAL-1]=f;
                    LOCALINVALID2OPT[1][NUM_INVALIDLOCAL-1]=f2;
                }
            }
        }
    }free(VariableFlag);
    
    //#temporary redundant activity (assume all activity A.A=A )
    LOCALINVALID2OPT[0]=(int*)realloc(LOCALINVALID2OPT[0], sizeof(int)*(NUM_INVALIDLOCAL+NUM_ACTIVITY));
    LOCALINVALID2OPT[1]=(int*)realloc(LOCALINVALID2OPT[1], sizeof(int)*(NUM_INVALIDLOCAL+NUM_ACTIVITY));
    for(int f=0;f<NUM_ACTIVITY;f++)
    {
        LOCALINVALID2OPT[0][NUM_INVALIDLOCAL+f]=f;
        LOCALINVALID2OPT[1][NUM_INVALIDLOCAL+f]=f;
    }
    NUM_INVALIDLOCAL+=NUM_ACTIVITY;
}

void NTgenVariablenActivityfromFile()
{
    char *buffer,*buffer2,*PCH;
    char str[NTDEF_MAXSTRSIZE],str2[NTDEF_MAXSTRSIZE],str3[NTDEF_MAXSTRSIZEm];
    NTSTRCT_STRING* string;
    long long1;
    int vari1;
    
    //make activity list
    FH=fopen(NTFile_LOG, "w");
    buffer=NTf_readWholeTextFile(NTFile_Currentactivitylist, &long1);
    NUM_ACTIVITY=NTf_CountNumSectionwDelimitor(buffer, ";\n");
    buffer2=(char*)malloc(sizeof(char)*(strlen(buffer)+1));
    strcpy(buffer2, buffer);
    string=(NTSTRCT_STRING*)malloc(sizeof(NTSTRCT_STRING)*NUM_ACTIVITY);
    //char **AA=(char**)malloc(sizeof(char)*1);
    //char **AA2=(char**)malloc(sizeof(char)*1);
    PCH=strtok(buffer2, ";\n");
    vari1=0;
    while (strcmp(PCH, "//"))
    {
        strcpy(string[vari1].s, PCH);
        PCH=strtok(NULL, ";\n");vari1++;
    }
    
    
    
    free(buffer2);
    if(ACTIVITY_LIST==NULL)
        ACTIVITY_LIST=(NTSTRCT_ACTIVITY*)malloc(sizeof(NTSTRCT_ACTIVITY)*NUM_ACTIVITY);//#global var
    
    for(int f=0;f<NUM_ACTIVITY;f++)
    {
        strcpy(str, string[f].s);
        PCH=strtok(str, ",");
        strcpy(ACTIVITY_LIST[f].Activityname, PCH);PCH=strtok(NULL, ",");
        ACTIVITY_LIST[f].Weight=atoi(PCH);PCH=strtok(NULL, ",");
        vari1=0;
        while (strcmp(PCH, "e"))
        {vari1++;PCH=strtok(NULL, ",");}
        ACTIVITY_LIST[f].precon_num=vari1;PCH=strtok(NULL, ",");
        //printf("Start %s |||| %s %d\n",string[f].s,string[10].s,f);
        ACTIVITY_LIST[f].precon=(NTSTRCT_STRING*)malloc(sizeof(NTSTRCT_STRING)*vari1);

        vari1=0;
        while (PCH!=NULL)
        {vari1++;PCH=strtok(NULL, ",");}
        ACTIVITY_LIST[f].effect_num=vari1;
        ACTIVITY_LIST[f].effect=(NTSTRCT_STRING*)malloc(sizeof(NTSTRCT_STRING)*vari1);
        ACTIVITY_LIST[f].effect_var=(NTSTRCT_STRING*)malloc(sizeof(NTSTRCT_STRING)*vari1);
        
        strcpy(str, string[f].s);PCH=strtok(str, ",");PCH=strtok(NULL, ",");PCH=strtok(NULL, ",");
        vari1=0;
        while (strcmp(PCH, "e"))
        {strcpy(ACTIVITY_LIST[f].precon[vari1].s, PCH);PCH=strtok(NULL, ",");vari1++;}
        PCH=strtok(NULL, ",");vari1=0;
        while (PCH!=NULL)
        {strcpy(ACTIVITY_LIST[f].effect[vari1].s, PCH);PCH=strtok(NULL, ",");vari1++;}
        for(int ff=0;ff<ACTIVITY_LIST[f].effect_num;ff++)
        {
            char str2[NTDEF_MAXSTRSIZE];
            strcpy(str, ACTIVITY_LIST[f].effect[ff].s);
            PCH=strtok(str, " ");
            strcpy(ACTIVITY_LIST[f].effect_var[ff].s, PCH);
            PCH=strtok(NULL, ",");str2[0]='\0';
            while (PCH!=NULL)
            {
                strcat(str2, PCH);strcat(str2, " ");
                PCH=strtok(NULL, ",");
            }
            strcat(str2, "\0");
            strcpy(ACTIVITY_LIST[f].effect[ff].s, str2);
        }
    }
    free(string);free(buffer);
    
    //make variable list
    buffer=NTf_readWholeTextFile(NTFile_CurrentVariableValueInit, &long1);
    NUM_VARIABLE=NTf_CountNumSectionwDelimitor(buffer, ";\n");
    
    if(VARIABLE_LIST==NULL)
        VARIABLE_LIST=(NTSTRCT_VARIABLE*)malloc(sizeof(NTSTRCT_VARIABLE)*NUM_VARIABLE);//#global var
    string=(NTSTRCT_STRING*)malloc(sizeof(NTSTRCT_STRING)*NUM_VARIABLE);
    buffer2=(char*)malloc(sizeof(char)*(strlen(buffer)+1));
    strcpy(buffer2, buffer);
    PCH=strtok(buffer2, ";\n");
    vari1=0;
    while (vari1<NUM_VARIABLE)
    {
        strcpy(string[vari1].s, PCH);
        PCH=strtok(NULL, ";\n");vari1++;
    }
    
    for(int f=0;f<NUM_VARIABLE;f++)
    {
        char str2[NTDEF_MAXSTRSIZEm];
        strcpy(str2, string[f].s);
        PCH=strtok(str2, " ");
        strcpy(VARIABLE_LIST[f].Variablename, PCH);
        PCH=strtok(NULL, " ");
        if(!strcmp(PCH, "var"))
            VARIABLE_LIST[f].type='v';
        else if(!strcmp(PCH, "res"))
            VARIABLE_LIST[f].type='r';
        else if(!strcmp(PCH, "dyres"))
            VARIABLE_LIST[f].type='d';
        else{printf("ERROR 1 wrong variable type\n");exit(1);}//wrong type
        PCH=strtok(NULL, " ");
        if(!strcmp(PCH, "b"))
            VARIABLE_LIST[f].sort='b';
        else if(!strcmp(PCH, "i"))
            VARIABLE_LIST[f].sort='i';
        else if(!strcmp(PCH, "I"))
            VARIABLE_LIST[f].sort='I';
        else{printf("ERROR 2 wrong variable sort\n");exit(2);}//wrong sort
        PCH=strtok(NULL, " ");
        if(VARIABLE_LIST[f].sort=='i' || VARIABLE_LIST[f].sort=='b' || VARIABLE_LIST[f].sort=='I' )
            VARIABLE_LIST[f].val=atoi(PCH);
        else {printf("ERROR 3 wrong value based on sort sort\n");exit(3);}//wrong value based on sort
    }
    free(buffer);free(buffer2);
        free(string);
    
    //Make reverse activity list
    //#this is temporary as currently, only bool and I variables are assumed
    
    REVACTVTY_LIST=(NTSTRCT_ACTYREV*)malloc(sizeof(NTSTRCT_ACTYREV)*(2*NUM_VARIABLE));//#global var
    for(int f=0;f<(2*NUM_VARIABLE);f++)REVACTVTY_LIST[f].Flag=0;
    NUM_REVACTIVITY=0;
    for(int f=0;f<NUM_VARIABLE;f++)
    {
        if(VARIABLE_LIST[f].sort=='b')
        {
            strcpy(REVACTVTY_LIST[2*f].Variablename, VARIABLE_LIST[f].Variablename);
            REVACTVTY_LIST[2*f].val=0;
            REVACTVTY_LIST[2*f].sort=VARIABLE_LIST[f].sort;
            strcpy(REVACTVTY_LIST[2*f].relation, "=");
            REVACTVTY_LIST[2*f].condition[0]='\0';
            REVACTVTY_LIST[2*f].Flag=0;
            strcpy(REVACTVTY_LIST[2*f+1].Variablename, VARIABLE_LIST[f].Variablename);
            REVACTVTY_LIST[2*f+1].val=1;
            REVACTVTY_LIST[2*f+1].sort=VARIABLE_LIST[f].sort;
            strcpy(REVACTVTY_LIST[2*f+1].relation, "=");
            REVACTVTY_LIST[2*f+1].condition[0]='\0';
            REVACTVTY_LIST[2*f+1].Flag=0;
            
            
            //when 0
            bool Flag=0;
            strcpy(str, "(or ");
            char* varname=VARIABLE_LIST[f].Variablename;
            for(int f2=0;f2<NUM_ACTIVITY;f2++)
            {
                for(int f3=0;f3<ACTIVITY_LIST[f2].effect_num;f3++)
                    if(!strcmp(varname, ACTIVITY_LIST[f2].effect_var[f3].s) && strcmp("true ", ACTIVITY_LIST[f2].effect[f3].s))
                    {
                        str2[0]='\0';
                        strcat(str2, "(and ");
                        for(int f4=0;f4<ACTIVITY_LIST[f2].precon_num;f4++)
                            strcat(str2, ACTIVITY_LIST[f2].precon[f4].s);
                        if(ACTIVITY_LIST[f2].precon_num>0)Flag=1;
                        if(strcmp("false ", ACTIVITY_LIST[f2].effect[f3].s))
                        {
                            sprintf(str3, "(= %s false)",ACTIVITY_LIST[f2].effect[f3].s);
                            strcat(str2, str3);Flag=1;
                        }
                        strcat(str2, ")");
                        strcat(str, str2);
                        break;
                    }
            }
            strcat(str, " false)");
            if(Flag && VARIABLE_LIST[f].type!='r')//#res not considered as rev activity
            {
                strcpy(REVACTVTY_LIST[2*f].condition, str);
                REVACTVTY_LIST[2*f].Flag=1;
                NUM_REVACTIVITY++;
            }
            else REVACTVTY_LIST[2*f].Flag=0;
            
            //when 1
            Flag=0;
            strcpy(str, "(or ");
            for(int f2=0;f2<NUM_ACTIVITY;f2++)
            {
                for(int f3=0;f3<ACTIVITY_LIST[f2].effect_num;f3++)
                    if(!strcmp(varname, ACTIVITY_LIST[f2].effect_var[f3].s) && strcmp("false ", ACTIVITY_LIST[f2].effect[f3].s))
                    {
                        str2[0]='\0';
                        strcat(str2, "(and ");
                        for(int f4=0;f4<ACTIVITY_LIST[f2].precon_num;f4++)
                            strcat(str2, ACTIVITY_LIST[f2].precon[f4].s);
                        if(ACTIVITY_LIST[f2].precon_num>0)Flag=1;
                        if(strcmp("true ", ACTIVITY_LIST[f2].effect[f3].s))
                        {
                            sprintf(str3, "(= %s true)",ACTIVITY_LIST[f2].effect[f3].s);
                            strcat(str2, str3);Flag=1;
                        }
                        strcat(str2, ")");
                        strcat(str, str2);
                        break;
                    }
            }
            strcat(str, " false)");
            if(Flag && VARIABLE_LIST[f].type!='r')//#res not considered as rev activity
            {
                strcpy(REVACTVTY_LIST[2*f+1].condition, str);
                REVACTVTY_LIST[2*f+1].Flag=1;
                NUM_REVACTIVITY++;
            }
            else REVACTVTY_LIST[2*f+1].Flag=0;
        }
        else if(VARIABLE_LIST[f].sort=='I')
        {
            strcpy(REVACTVTY_LIST[2*f].Variablename, VARIABLE_LIST[f].Variablename);
            REVACTVTY_LIST[2*f].val=-1;
            REVACTVTY_LIST[2*f].sort=VARIABLE_LIST[f].sort;
            strcpy(REVACTVTY_LIST[2*f].relation, ">");
            REVACTVTY_LIST[2*f].condition[0]='\0';
            REVACTVTY_LIST[2*f].Flag=0;
            strcpy(REVACTVTY_LIST[2*f+1].Variablename, VARIABLE_LIST[f].Variablename);
            REVACTVTY_LIST[2*f+1].val=0;
            REVACTVTY_LIST[2*f+1].sort=VARIABLE_LIST[f].sort;
            strcpy(REVACTVTY_LIST[2*f+1].relation, "<");
            REVACTVTY_LIST[2*f+1].condition[0]='\0';
            REVACTVTY_LIST[2*f+1].Flag=0;
            
            //when not equal -1
            bool Flag=0;
            strcpy(str, "(or ");
            char* varname=VARIABLE_LIST[f].Variablename;
            for(int f2=0;f2<NUM_ACTIVITY;f2++)
            {
                for(int f3=0;f3<ACTIVITY_LIST[f2].effect_num;f3++)
                    if(!strcmp(varname, ACTIVITY_LIST[f2].effect_var[f3].s))
                    {
                        str2[0]='\0';
                        strcat(str2, "(and ");
                        for(int f4=0;f4<ACTIVITY_LIST[f2].precon_num;f4++)
                            strcat(str2, ACTIVITY_LIST[f2].precon[f4].s);
                        if(ACTIVITY_LIST[f2].precon_num>0)Flag=1;
                        //what about A:=B as effect
//                        if(strcmp("false ", ACTIVITY_LIST[f2].effect[f3]))
//                        {
//                            sprintf(str3, "(= %s false)",ACTIVITY_LIST[f2].effect[f3]);
//                            strcat(str2, str3);Flag=1;
//                        }
                        strcat(str2, ")");
                        strcat(str, str2);
                        break;
                    }
            }
            strcat(str, " false)");
            if(Flag && VARIABLE_LIST[f].type!='r')//#res not considered as rev activity
            {
                strcpy(REVACTVTY_LIST[2*f].condition, str);
                REVACTVTY_LIST[2*f].Flag=1;
                NUM_REVACTIVITY++;
            }
            else REVACTVTY_LIST[2*f].Flag=0;

            
        }
    }
    
    
    

    
    //make goal list
    buffer=NTf_readWholeTextFile(NTFile_Currentgoallist, &long1);
    NUM_GOAL=NTf_CountNumSectionwDelimitor(buffer, ";\n");
    buffer2=(char*)malloc(sizeof(char)*(strlen(buffer)+1));
    strcpy(buffer2, buffer);
    GOAL_LIST=(NTSTRCT_GOAL*)malloc(sizeof(NTSTRCT_GOAL)*NUM_GOAL);//#global var
    PCH=strtok(buffer2, ";\n");
    vari1=0;
    while (strcmp(PCH, "//"))
    {
        strcpy(GOAL_LIST[vari1].Goal, PCH);
        PCH=strtok(NULL, ";\n");vari1++;
    }
    free(buffer);free(buffer2);
    //#currently all goal weights are set to NTDEF_NUMSEQUENCE+1+NUM_REVACTIVITY
    for(int f=0;f<NUM_GOAL;f++)
        GOAL_LIST[f].Weight=NTDEF_NUMSEQUENCE+1+NUM_REVACTIVITY+NUM_VARIABLE*NTDEF_ChangedVarCost;
    //#currently all revactivity weights are set to NTDEF_REVACTWEIGHT;
    for(int f=0;f<(NUM_VARIABLE*2);f++)
        REVACTVTY_LIST[f].Weight=NTDEF_REVACTWEIGHT;
    
    //generate local inconsistency array for Memetic local search
    NT_genLocalInconsistencyforMemetic();
    
    for(int f=0;f<NUM_GOAL;f++)
        printf("Goal %s %d\n",GOAL_LIST[f].Goal,GOAL_LIST[f].Weight);
    for(int f=0;f<(NUM_VARIABLE*2);f++)
        if(REVACTVTY_LIST[f].Flag==1)
            printf("rev (%s %s %d)=>(%s) w=%d\n",REVACTVTY_LIST[f].Variablename,REVACTVTY_LIST[f].relation,REVACTVTY_LIST[f].val,REVACTVTY_LIST[f].condition,REVACTVTY_LIST[f].Weight);
    
}

int NTCheck_Get_Val_VariableList(const char* Name,int *Value,char* Sort,char* Type )
{//return -1 if no variable found. return index if found
    int f;bool Flag=0;;
    for(f=0;f<NUM_VARIABLE;f++)
        if(!strcmp(Name, VARIABLE_LIST[f].Variablename))
        {
            *Value=VARIABLE_LIST[f].val;
            *Sort=VARIABLE_LIST[f].sort;
            *Type=VARIABLE_LIST[f].type;
            Flag=1;break;
        }
    if(Flag)return f;
    else return -1;
}

Z3_context NTf_mk_context()
{
    Z3_context CONT1;
    Z3_config  cfg;
    cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "MODEL", "true");
    CONT1=Z3_mk_context(cfg);
    Z3_del_config(cfg);
    return CONT1;
}

int NTf_storeModelinNTSTRCTSOmeVariableNoOneUse(Z3_context ctx,Z3_model m)
{
    int ERRR=1;
    int RETURNV=-1;
    unsigned num_constants;
    char str1[50];
    char CHR1;
    int VAL1;
    Z3_symbol Symbol1;
    Z3_ast AST1,AST2;
    num_constants = Z3_get_model_num_constants(ctx, m);
    for(int f=0;f<num_constants;f++)
    {
        Z3_func_decl cnst = Z3_get_model_constant(ctx, m, f);
        Symbol1 = Z3_get_decl_name(ctx, cnst);
        AST1 = Z3_mk_app(ctx, cnst, 0, 0);
        AST2=AST1;
        Z3_eval(ctx, m, AST1, &AST2);
        Z3_sort Sort1 = Z3_get_sort(ctx, AST2);
        switch (Z3_get_sort_kind(ctx, Sort1))
        {
            case Z3_BOOL_SORT:
                CHR1='b';
                break;
            case Z3_INT_SORT:
                CHR1='i';
                break;
            default:
                printf("\nError! Wrong sort ");exit(-1);
                break;
        }
        
        if(Z3_get_ast_kind(ctx, AST2)==Z3_NUMERAL_AST)
        {
            VAL1=atoi(Z3_get_numeral_string(ctx, AST2));
        }
        else //note: assume is bool
        {
            char* PCH;
            Z3_app app = Z3_to_app(ctx, AST2);
            Z3_func_decl D = Z3_get_app_decl(ctx, app);
            strcpy(str1, Z3_func_decl_to_string(ctx, D));
            PCH=strtok(str1, " ");
            PCH=strtok(NULL, " ");
            if(!strcmp(PCH, "true"))VAL1=1;
            else VAL1=0;
        }
        strcpy(str1, Z3_get_symbol_string(ctx, Symbol1));
        
        if(!strcmp(str1, "SomeVariableNoOneUse"))
        {
            RETURNV=VAL1;
            ERRR=0;
        }
    }
    if(ERRR==1){printf("ERROR105\n");exit(5);}
    return RETURNV;
}

int NTf_SATtest(const char* STR)
{
    int ResultFlag;
    int num_formulas=0;
    Z3_context ctx=NTf_mk_context();
    Z3_parse_smtlib_string(ctx,STR ,0, 0, 0, 0, 0, 0);
    num_formulas = Z3_get_smtlib_num_formulas(ctx);
    for (int i = 0; i < num_formulas; i++) {
        Z3_ast f = Z3_get_smtlib_formula(ctx, i);
        Z3_assert_cnstr(ctx, f);
    }
    Z3_model m      = 0;
    Z3_lbool result = Z3_check_and_get_model(ctx, &m);
    switch (result) {
        case Z3_L_FALSE:
            ResultFlag=0;
            break;
        case Z3_L_UNDEF:
            ResultFlag=2;
            break;
        case Z3_L_TRUE:
            ResultFlag=1;
            break;
    }
    if (m) Z3_del_model(ctx, m);
    Z3_del_context(ctx);
    return ResultFlag;
}


int NTf_getSOmeVariableNoOneUse(const char* STR)
{
    int ResultFlag;
    int RESS;
    int num_formulas=0;
    Z3_context ctx=NTf_mk_context();
    Z3_parse_smtlib_string(ctx,STR ,0, 0, 0, 0, 0, 0);
    num_formulas = Z3_get_smtlib_num_formulas(ctx);
    for (int i = 0; i < num_formulas; i++) {
        Z3_ast f = Z3_get_smtlib_formula(ctx, i);
        Z3_assert_cnstr(ctx, f);
    }
    Z3_model m      = 0;
    Z3_lbool result = Z3_check_and_get_model(ctx, &m);
    switch (result) {
        case Z3_L_FALSE:
            ResultFlag=0;
            break;
        case Z3_L_UNDEF:
            ResultFlag=2;
            RESS=NTf_storeModelinNTSTRCTSOmeVariableNoOneUse(ctx, m);
            break;
        case Z3_L_TRUE:
            ResultFlag=1;
            RESS=NTf_storeModelinNTSTRCTSOmeVariableNoOneUse(ctx, m);
            break;
    }
    if (m) Z3_del_model(ctx, m);
    Z3_del_context(ctx);
    return RESS;
}



int NTLBCost_discreteActivity(int Act[NTDEF_NUMSEQUENCE-1],int initState[])
{
    //what about activity=-1
    int REVCost,ACTCost,GOALCost,STACost;
    static int *State,*State2,*StateFlag;
    char* PCH;
    char str[NTDEF_MAXSTRSIZE],str2[NTDEF_MAXSTRSIZE];
    if(State==NULL)State=(int*)malloc(sizeof(int)*NUM_VARIABLE);
    if(State2==NULL)State2=(int*)malloc(sizeof(int)*NUM_VARIABLE);
    if(StateFlag==NULL)StateFlag=(int*)malloc(sizeof(int)*NUM_VARIABLE);
    for(int f=0;f<NUM_VARIABLE;f++)
        State[f]=initState[f];
    for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)
    {
        for(int f2=0;f2<NUM_VARIABLE;f2++)
            StateFlag[f2]=0;
        if(Act[f]!=-1)
        {
            for(int f2=0;f2<ACTIVITY_LIST[Act[f]].effect_num;f2++)
            {
                strcpy(str, ACTIVITY_LIST[Act[f]].effect[f2].s);
                PCH=strtok(str, " ");
                char varsort1,var2;int var3;
                char* varname4=ACTIVITY_LIST[Act[f]].effect_var[f2].s;
                int varindex=NTCheck_Get_Val_VariableList(varname4, &var3, &varsort1, &var2);
                StateFlag[varindex]=1;
                if(varsort1=='i')
                    sprintf(str2, "(");//changed
                    //sprintf(str2, "(benchmark tst :extrafuns((SomeVariableNoOneUse Int)) :formula(= SomeVariableNoOneUse ");
                else if(varsort1=='b')
                    sprintf(str2, "(");//changed
                else if(varsort1=='I')
                    sprintf(str2, "(");//changed
                else {printf("ERROR06\n"),exit(6);}
                
                while (PCH!=NULL)
                {
                    char Sort,Type;
                    int Val;
                    int Flag=NTCheck_Get_Val_VariableList(PCH, &Val, &Sort, &Type);
                    if(Flag==-1)
                    {
                        strcat(str2, PCH);strcat(str2, " ");
                    }
                    else
                    {
                        char strr1[NTDEF_MAXSTRSIZEs];
                        Val=State[Flag];
                        if(Sort=='i') sprintf(strr1, "%d ",Val);
                        else if(Sort=='I')sprintf(strr1, "%d ",Val);
                        else if(Sort=='b'){
                            if(Val==0) sprintf(strr1, "0 ");
                            else sprintf(strr1, "1 ");}
                        strcat(str2, strr1);
                    }
                    PCH=strtok(NULL, " ");
                }
                strcat(str2, ") ");
                State2[varindex]=NTL_GetValue(str2);//NTf_getSOmeVariableNoOneUse(str2);
            }
        }
        
        for(int f2=0;f2<NUM_VARIABLE;f2++)
            if(StateFlag[f2]==1) State[f2]=State2[f2];
          //printf("%d %d %d %d \n",f+1,State[0],State[1],State[2]);//print out state for every seq
    }
    //calc REV cost
    GOALCost=0;REVCost=0;ACTCost=0;STACost=0;
    for(int f=0;f<(NUM_VARIABLE*2);f++)
    {
        if(REVACTVTY_LIST[f].Flag==1)
        {
            for(int fvar=0;fvar<NUM_VARIABLE;fvar++)
            {
                if(!strcmp(REVACTVTY_LIST[f].Variablename, VARIABLE_LIST[fvar].Variablename) )
                {
                    if(VARIABLE_LIST[fvar].sort=='i' || VARIABLE_LIST[fvar].sort=='I')
                    {
                        sprintf(str, "((%s %d %d)) ",REVACTVTY_LIST[f].relation,initState[fvar],REVACTVTY_LIST[f].val);//changed
                        //sprintf(str, "(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse (%s %d %d)) ",REVACTVTY_LIST[f].relation,initState[fvar],REVACTVTY_LIST[f].val);
                    }
                    else if(VARIABLE_LIST[fvar].sort=='b')
                    {
                        char strr1[NTDEF_MAXSTRSIZEs],strr2[NTDEF_MAXSTRSIZEs];
                        if(initState[fvar]==0)sprintf(strr1, "0");
                        else sprintf(strr1, "1");
                        if(REVACTVTY_LIST[f].val==0)sprintf(strr2, "0");
                        else sprintf(strr2, "1");
                        sprintf(str, "((%s %s %s))",REVACTVTY_LIST[f].relation,strr1,strr2);//changed
                        //sprintf(str, "(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse (%s %s %s))",REVACTVTY_LIST[f].relation,strr1,strr2);
                    }
                    int Flag2=NTL_GetValue(str);//NTf_getSOmeVariableNoOneUse(str);
                    if(Flag2==0)//if ok, start eva whether d coniditon will meet or not to calc cost
                    {
                        char Sort,Type;
                        int Val;
                        if(VARIABLE_LIST[fvar].sort=='i' || VARIABLE_LIST[fvar].sort=='I')
                        {
                            sprintf(str, "((=> (%s %d %d) ",REVACTVTY_LIST[f].relation,REVACTVTY_LIST[f].val,State[fvar]);//changed
                            //sprintf(str, "(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse (=> (%s %d %d) ",REVACTVTY_LIST[f].relation,REVACTVTY_LIST[f].val,State[fvar]);
                        }
                        else if(VARIABLE_LIST[fvar].sort=='b')
                        {
                            char strr1[NTDEF_MAXSTRSIZEs],strr2[NTDEF_MAXSTRSIZEs];
                            if(REVACTVTY_LIST[f].val==0)strcpy(strr1, "0");
                            else strcpy(strr1, "1");
                            if(State[fvar]==0)strcpy(strr2, "0");
                            else strcpy(strr2, "1");
                            sprintf(str, "((=> (%s %s %s) ",REVACTVTY_LIST[f].relation,strr1,strr2);//changed
                            //sprintf(str, "(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse (=> (%s %s %s) ",REVACTVTY_LIST[f].relation,strr1,strr2);
                        }
                        
                        strcpy(str2, REVACTVTY_LIST[f].condition);
                        PCH=strtok(str2, " ");
                        while (PCH!=NULL)
                        {
                            int varindex=NTCheck_Get_Val_VariableList(PCH, &Val, &Sort, &Type);
                            if(varindex==-1)
                            {strcat(str, PCH);strcat(str, " ");}
                            else
                            {
                                if(Sort=='i' || Sort=='I')
                                {
                                    char strr1[NTDEF_MAXSTRSIZEs];
                                    sprintf(strr1, "%d ",State[varindex]);
                                    strcat(str, strr1);
                                }
                                else if(Sort=='b')
                                {
                                    if(State[varindex]==0) strcat(str, "0 ");
                                    else strcat(str, "1 ");
                                }
                            }
                            PCH=strtok(NULL, " ");
                        }
                        strcat(str, "))");
                        int Ress=NTL_GetValue(str);//NTf_getSOmeVariableNoOneUse(str);
                        if(Ress==0)
                            REVCost+=REVACTVTY_LIST[f].Weight;
                        //printf("%s %s      %d\n",VARIABLE_LIST[fvar].Variablename,str,Ress);
                        
                    }//end if ok, start ...
                    break;
                }
            }
        }
    }
    //calc Goal cost
    for(int f=0;f<NUM_GOAL;f++)
    {
        sprintf(str, "(");//changed
        //sprintf(str, "(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse ");
        strcpy(str2, GOAL_LIST[f].Goal);
        PCH=strtok(str2, " ");
        char strr1[NTDEF_MAXSTRSIZE],strr2[NTDEF_MAXSTRSIZEs];
        strr1[0]='\0';
        while (PCH!=NULL)
        {
            char Sort,Type;
            int Val;
            int varindex=NTCheck_Get_Val_VariableList(PCH, &Val, &Sort, &Type);
            if(varindex!=-1)
            {
                if(VARIABLE_LIST[varindex].sort=='i' || VARIABLE_LIST[varindex].sort=='I')
                {
                    sprintf(strr2, "%d ",State[varindex]);
                    strcat(strr1, strr2);
                }
                else if(VARIABLE_LIST[varindex].sort=='b')
                {
                    if(State[varindex]==0) strcat(strr1, "0 ");
                    else strcat(strr1, "1 ");
                }
            }
            else
            {
                strcat(strr1, PCH);strcat(strr1, " ");
            }
            PCH=strtok(NULL, " ");
        }
        strcat(str, strr1);strcat(str, ")");
    
        int Ress=NTL_GetValue(str);//NTf_getSOmeVariableNoOneUse(str);
        if(Ress==0)
            GOALCost+=GOAL_LIST[f].Weight;
    }
    //Action cost
    for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)
        if(Act[f]!=-1) ACTCost+=ACTIVITY_LIST[Act[f]].Weight;
        else ACTCost+=NTDEF_NOOPWEIGHT;
    
    //State alteration cost
    for(int f=0;f<NUM_VARIABLE;f++)
        if(VARIABLE_LIST[f].val!=State[f])STACost+=NTDEF_ChangedVarCost;
    
    
    return GOALCost+ACTCost+REVCost+STACost;
}

int NTLBCost_discreteActivityTEST(int Act[NTDEF_NUMSEQUENCE-1],int initState[])
{
    //what about activity=-1
    for(int f=0;f<NUM_VARIABLE;f++)printf("V%d=%d ",f,initState[f]);printf("\n");
    int REVCost,ACTCost,GOALCost,STACost;
    static int *State,*State2,*StateFlag;
    char* PCH;
    char str[NTDEF_MAXSTRSIZE],str2[NTDEF_MAXSTRSIZE];
    if(State==NULL)State=(int*)malloc(sizeof(int)*NUM_VARIABLE);
    if(State2==NULL)State2=(int*)malloc(sizeof(int)*NUM_VARIABLE);
    if(StateFlag==NULL)StateFlag=(int*)malloc(sizeof(int)*NUM_VARIABLE);
    for(int f=0;f<NUM_VARIABLE;f++)
        State[f]=initState[f];
    for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)
    {
        for(int f2=0;f2<NUM_VARIABLE;f2++)
            StateFlag[f2]=0;
        if(Act[f]!=-1)
        {
            for(int f2=0;f2<ACTIVITY_LIST[Act[f]].effect_num;f2++)
            {
                strcpy(str, ACTIVITY_LIST[Act[f]].effect[f2].s);
                PCH=strtok(str, " ");
                char varsort1,var2;int var3;
                char* varname4=ACTIVITY_LIST[Act[f]].effect_var[f2].s;
                int varindex=NTCheck_Get_Val_VariableList(varname4, &var3, &varsort1, &var2);
                StateFlag[varindex]=1;
                if(varsort1=='i')
                    sprintf(str2, "(");//changed
                //sprintf(str2, "(benchmark tst :extrafuns((SomeVariableNoOneUse Int)) :formula(= SomeVariableNoOneUse ");
                else if(varsort1=='b')
                    sprintf(str2, "(");//changed
                else if(varsort1=='I')
                    sprintf(str2, "(");//changed
                else {printf("ERROR06\n"),exit(6);}
                
                while (PCH!=NULL)
                {
                    char Sort,Type;
                    int Val;
                    int Flag=NTCheck_Get_Val_VariableList(PCH, &Val, &Sort, &Type);
                    if(Flag==-1)
                    {
                        strcat(str2, PCH);strcat(str2, " ");
                    }
                    else
                    {
                        char strr1[NTDEF_MAXSTRSIZEs];
                        Val=State[Flag];
                        if(Sort=='i') sprintf(strr1, "%d ",Val);
                        else if(Sort=='I')sprintf(strr1, "%d ",Val);
                        else if(Sort=='b'){
                            if(Val==0) sprintf(strr1, "0 ");
                            else sprintf(strr1, "1 ");}
                        strcat(str2, strr1);
                    }
                    PCH=strtok(NULL, " ");
                }
                strcat(str2, ") ");
                State2[varindex]=NTL_GetValue(str2);//NTf_getSOmeVariableNoOneUse(str2);
            }
        }
        
        for(int f2=0;f2<NUM_VARIABLE;f2++)
            if(StateFlag[f2]==1) State[f2]=State2[f2];
        //printf("%d %d %d %d \n",f+1,State[0],State[1],State[2]);//print out state for every seq
    }
    //calc REV cost
    GOALCost=0;REVCost=0;ACTCost=0;STACost=0;
    for(int f=0;f<(NUM_VARIABLE*2);f++)
    {
        if(REVACTVTY_LIST[f].Flag==1)
        {
            for(int fvar=0;fvar<NUM_VARIABLE;fvar++)
            {
                if(!strcmp(REVACTVTY_LIST[f].Variablename, VARIABLE_LIST[fvar].Variablename) )
                {
                    if(VARIABLE_LIST[fvar].sort=='i' || VARIABLE_LIST[fvar].sort=='I')
                    {
                        sprintf(str, "((%s %d %d)) ",REVACTVTY_LIST[f].relation,initState[fvar],REVACTVTY_LIST[f].val);//changed
                        //sprintf(str, "(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse (%s %d %d)) ",REVACTVTY_LIST[f].relation,initState[fvar],REVACTVTY_LIST[f].val);
                    }
                    else if(VARIABLE_LIST[fvar].sort=='b')
                    {
                        char strr1[NTDEF_MAXSTRSIZEs],strr2[NTDEF_MAXSTRSIZEs];
                        if(initState[fvar]==0)sprintf(strr1, "0");
                        else sprintf(strr1, "1");
                        if(REVACTVTY_LIST[f].val==0)sprintf(strr2, "0");
                        else sprintf(strr2, "1");
                        sprintf(str, "((%s %s %s))",REVACTVTY_LIST[f].relation,strr1,strr2);//changed
                        //sprintf(str, "(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse (%s %s %s))",REVACTVTY_LIST[f].relation,strr1,strr2);
                    }
                    int Flag2=NTL_GetValue(str);//NTf_getSOmeVariableNoOneUse(str);
                    
                    //Check whether the condition for Revactivity variable=initial variable value. Continue if not the same
                    if(Flag2==0)//if ok, start eva whether d coniditon will meet or not to calc cost
                    {
                        char Sort,Type;
                        int Val;
                        if(VARIABLE_LIST[fvar].sort=='i' || VARIABLE_LIST[fvar].sort=='I')
                        {
                            sprintf(str, "((=> (%s %d %d) ",REVACTVTY_LIST[f].relation,REVACTVTY_LIST[f].val,State[fvar]);//changed
                            //sprintf(str, "(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse (=> (%s %d %d) ",REVACTVTY_LIST[f].relation,REVACTVTY_LIST[f].val,State[fvar]);
                        }
                        else if(VARIABLE_LIST[fvar].sort=='b')
                        {
                            char strr1[NTDEF_MAXSTRSIZEs],strr2[NTDEF_MAXSTRSIZEs];
                            if(REVACTVTY_LIST[f].val==0)strcpy(strr1, "0");
                            else strcpy(strr1, "1");
                            if(State[fvar]==0)strcpy(strr2, "0");
                            else strcpy(strr2, "1");
                            sprintf(str, "((=> (%s %s %s) ",REVACTVTY_LIST[f].relation,strr1,strr2);//changed
                            //sprintf(str, "(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse (=> (%s %s %s) ",REVACTVTY_LIST[f].relation,strr1,strr2);
                        }
                        
                        strcpy(str2, REVACTVTY_LIST[f].condition);
                        PCH=strtok(str2, " ");
                        while (PCH!=NULL)
                        {
                            int varindex=NTCheck_Get_Val_VariableList(PCH, &Val, &Sort, &Type);
                            if(varindex==-1)
                            {strcat(str, PCH);strcat(str, " ");}
                            else
                            {
                                if(Sort=='i' || Sort=='I')
                                {
                                    char strr1[NTDEF_MAXSTRSIZEs];
                                    sprintf(strr1, "%d ",State[varindex]);
                                    strcat(str, strr1);
                                }
                                else if(Sort=='b')
                                {
                                    if(State[varindex]==0) strcat(str, "0 ");
                                    else strcat(str, "1 ");
                                }
                            }
                            PCH=strtok(NULL, " ");
                        }
                        strcat(str, "))");
                        int Ress=NTL_GetValue(str);//NTf_getSOmeVariableNoOneUse(str);
                        if(Ress==0)
                            REVCost+=REVACTVTY_LIST[f].Weight;
                        //printf("%s %s      %d\n",VARIABLE_LIST[fvar].Variablename,str,Ress);
                        
                    }//end if ok, start ...
                    break;
                }
            }
        }
    }
    //calc Goal cost
    for(int f=0;f<NUM_GOAL;f++)
    {
        sprintf(str, "(");//changed
        //sprintf(str, "(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse ");
        strcpy(str2, GOAL_LIST[f].Goal);
        PCH=strtok(str2, " ");
        char strr1[NTDEF_MAXSTRSIZE],strr2[NTDEF_MAXSTRSIZEs];
        strr1[0]='\0';
        while (PCH!=NULL)
        {
            char Sort,Type;
            int Val;
            int varindex=NTCheck_Get_Val_VariableList(PCH, &Val, &Sort, &Type);
            if(varindex!=-1)
            {
                if(VARIABLE_LIST[varindex].sort=='i' || VARIABLE_LIST[varindex].sort=='I')
                {
                    sprintf(strr2, "%d ",State[varindex]);
                    strcat(strr1, strr2);
                }
                else if(VARIABLE_LIST[varindex].sort=='b')
                {
                    if(State[varindex]==0) strcat(strr1, "0 ");
                    else strcat(strr1, "1 ");
                }
            }
            else
            {
                strcat(strr1, PCH);strcat(strr1, " ");
            }
            PCH=strtok(NULL, " ");
        }
        strcat(str, strr1);strcat(str, ")");
        
        int Ress=NTL_GetValue(str);//NTf_getSOmeVariableNoOneUse(str);
        if(Ress==0)
            GOALCost+=GOAL_LIST[f].Weight;
    }
    //Action cost
    for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)
        if(Act[f]!=-1) ACTCost+=ACTIVITY_LIST[Act[f]].Weight;
        else ACTCost+=NTDEF_NOOPWEIGHT;
    
    //State alteration cost
    for(int f=0;f<NUM_VARIABLE;f++)
        if(VARIABLE_LIST[f].val!=State[f])STACost+=NTDEF_ChangedVarCost;
    
    printf("Goal %d act %d Rev %d StaCost %d\n\n",GOALCost,ACTCost,REVCost,STACost);
    return GOALCost+ACTCost+REVCost+STACost;
}


bool NT_checkpreconholdsornot(int Xc[],int ActivityNum)
{
    char str[NTDEF_MAXSTRSIZE],str2[NTDEF_MAXSTRSIZE];
    char *PCH;
    char Sort,Type;
    int Val;
    sprintf(str,"(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse (and ");
    for(int f=0;f<ACTIVITY_LIST[ActivityNum].precon_num;f++)
    {
        char strr1[NTDEF_MAXSTRSIZEs];
        strcpy(str2, ACTIVITY_LIST[ActivityNum].precon[f].s);
        PCH=strtok(str2, " ");
        while (PCH!=NULL)
        {
            int varindex=NTCheck_Get_Val_VariableList(PCH, &Val, &Sort, &Type);
            if(varindex==-1) {strcat(str, PCH);strcat(str, " ");}
            else
            {
                if(Sort=='i' || Sort=='I')
                {
                    sprintf(strr1, "%d ",Xc[varindex]);
                    strcat(str, strr1);
                }
                else if(Sort=='b')
                {
                    if(Xc[varindex]==0)strcpy(strr1, "false ");
                    else strcpy(strr1, "true ");
                    strcat(str, strr1);
                }
            }PCH=strtok(NULL, " ");
        }
    }strcat(str, "))");
    //printf("%s %d\n",str,ActivityNum);
    return NTf_getSOmeVariableNoOneUse(str);
}

void NT_manipstatefromacteffect(int Xc[],int Xout[],int ActivityNum)
{
    char str[NTDEF_MAXSTRSIZE];
    static int* StateFlag;
    char *PCH;
    if(StateFlag==NULL)StateFlag=(int*)malloc(sizeof(int)*NUM_VARIABLE);
    for(int f=0;f<NUM_VARIABLE;f++) {StateFlag[f]=0;Xout[f]=Xc[f];}
    for(int f=0;f<ACTIVITY_LIST[ActivityNum].effect_num;f++)
    {
        char strr1[NTDEF_MAXSTRSIZE];
        NTSTRCT_ACTIVITY At=ACTIVITY_LIST[ActivityNum];
        char Sort,Type;int Val;
        int varindex=NTCheck_Get_Val_VariableList(At.effect_var[f].s, &Val, &Sort, &Type);
        int StateUpdateIndex=varindex;
        if(varindex==-1){printf("Error07!!\n"),exit(7);}
        if(Sort=='i' || Sort=='I')
            sprintf(str,"(benchmark tst :extrafuns((SomeVariableNoOneUse Int)) :formula(= SomeVariableNoOneUse ");
        else if(Sort=='b')
            sprintf(str,"(benchmark tst :extrafuns((SomeVariableNoOneUse Bool)) :formula(= SomeVariableNoOneUse ");
        else {printf("Error09!\n"),exit(9);}
        strcpy(strr1, At.effect[f].s);
        PCH=strtok(strr1, " ");
        while (PCH!=NULL)
        {
            varindex=NTCheck_Get_Val_VariableList(PCH, &Val, &Sort, &Type);
            if(varindex==-1) {strcat(str, PCH);strcat(str, " ");}
            else
            {
                if(Sort=='i' || Sort=='I')
                {
                    char strr2[NTDEF_MAXSTRSIZEs];
                    sprintf(strr2, "%d ",Xc[varindex]);
                    strcat(str, strr2);
                }
                else if(Sort=='b')
                {
                    if(Xc[varindex]==0) strcat(str, "false ");
                    else strcat(str, "true ");
                }
                else {printf("Error08!\n"),exit(8);}
            }PCH=strtok(NULL, " ");
        }
        strcat(str, ")");
        int Ress=NTf_getSOmeVariableNoOneUse(str);
        StateFlag[StateUpdateIndex]=1;
        Xout[StateUpdateIndex]=Ress;
    }
}

bool NTL_IsActivityRedundant(int CSC[],int Act)
{
    char str[NTDEF_MAXSTRSIZE],str2[NTDEF_MAXSTRSIZE];
    char *PCH;
    static int *State;
    if(State==NULL)State=(int*)malloc(sizeof(int)*NUM_VARIABLE);
    for(int f=0;f<NUM_VARIABLE;f++)State[f]=CSC[f];
    for(int f=0;f<ACTIVITY_LIST[Act].effect_num;f++)
    {
        NTSTRCT_ACTIVITY At=ACTIVITY_LIST[Act];
        char Sort,Type;
        int Val;
        int varindex1=NTCheck_Get_Val_VariableList(At.effect_var[f].s, &Val, &Sort, &Type);
        strcpy(str, "(");
        strcpy(str2, At.effect[f].s);
        PCH=strtok(str2, " ");
        while(PCH!=NULL)
        {
            int varindex2=NTCheck_Get_Val_VariableList(PCH, &Val, &Sort, &Type);
            if(varindex2!=-1)
            {
                char strr[NTDEF_MAXSTRSIZEs];
                sprintf(strr," %d ",CSC[varindex2]);
                strcat(str, strr);
            }
            else strcat(str, PCH);
            PCH=strtok(NULL, " ");
        }
        strcat(str, " )");
        State[varindex1]=NTL_GetValue(str);
    }
    bool RedundantFlag=1;
    for(int f=0;f<NUM_VARIABLE;f++)
        if(CSC[f]!=State[f]){RedundantFlag=0;break;}
    return RedundantFlag;
}

int NTMEMETIC(int NA,int TS,int CS, int State[],int** Local2opt,int ArraySize )
{
    //NA=num of activity, TS=total activity sequence, CS=number of activities that need to be generated
    //number of -1 activity need to be evaluated is TS-CS
    //printf("QQQ %d %d\n",CS,TS-CS);
    //subtract (TS-CS)*NoopWeight
    return 0;
}

int NTMEMETIC2(int NA,int TS,int CS, int State[],int** Local2opt,int ArraySize )
{
    //NA=num of activity, TS=total activity sequence, CS=number of activities that need to be generated
    //number of -1 activity need to be evaluated is TS-CS
    //printf("QQQ %d %d\n",CS,TS-CS);
    
    static int* Act;
    if(Act==NULL)Act=(int*)malloc(sizeof(int)*TS);
    for(int f=0;f<TS;f++)Act[f]=-1;
    for(int f=0;f<CS;f++)
    {
        for(int f2=0;f2<=NA;f2++)//Act NA is -1
        {
            
        }
    }
    
    
    //subtract (TS-CS)*NoopWeight
    return 0;
}

int NTL_2ndCSCCheck(int CSCc2[],int Xc[])
{
    for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)printf("%d ",CSCc2[f]);printf("\n");
    static int *State,*State2;
    bool InvalidFlag=0;
    int TotalCost=1000000;
    if(State==NULL)State=(int*)malloc(sizeof(int)*NUM_VARIABLE);
    if(State2==NULL)State2=(int*)malloc(sizeof(int)*NUM_VARIABLE);
    for(int f=0;f<NUM_VARIABLE;f++){State[f]=Xc[f];State2[f]=Xc[f];}
    for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)
    {
        if(CSCc2[f]>=0 && ACTIVITY_LIST[CSCc2[f]].precon_num!=0)
        {
            bool PreconFlag=NT_checkpreconholdsornot(State, CSCc2[f]);
            if(PreconFlag==1)
            {
//                for(int fff=0;fff<NUM_VARIABLE;fff++)printf("v=%d ",State[fff]);
//                printf("Precon=(%d) \n",CSCc2[f]);
                NT_manipstatefromacteffect(State, State2, CSCc2[f]);
                for(int f2=0;f2<NUM_VARIABLE;f2++)State[f2]=State2[f2];
            }
            else
            {
                InvalidFlag=1;
//                for(int fff=0;fff<NUM_VARIABLE;fff++)printf("v=%d ",State[fff]);
//                printf("act= %d\n",CSCc2[f]);
                break;
            }
        }
        else if(CSCc2[f]>=0)
        {
//            for(int fff=0;fff<NUM_VARIABLE;fff++)printf("v=%d ",State[fff]);
//            printf("act2= %d\n",CSCc2[f]);
            NT_manipstatefromacteffect(State, State2, CSCc2[f]);
            for(int f2=0;f2<NUM_VARIABLE;f2++)State[f2]=State2[f2];
        }
    }
    if(InvalidFlag==0)
        TotalCost=NTLBCost_discreteActivityTEST(CSCc2, State);
    return TotalCost;
}

void NT_BnB(int Cc,int tc,int Xc[],int CSC[],int EstTotalCost)
{//Cc Current cost tc Current sequence Xc Current state CSC Current activity sequence
    int *LB_ori,*LB_sort,*LB_sort_Act,*LB_ori_flag,*CSC2;
    int *State1;
        State1=(int*)malloc(sizeof(int)*NUM_VARIABLE);
        LB_ori=(int*)malloc(sizeof(int)*(NUM_ACTIVITY+1));
        LB_sort=(int*)malloc(sizeof(int)*(NUM_ACTIVITY+1));
        LB_sort_Act=(int*)malloc(sizeof(int)*(NUM_ACTIVITY+1));
        LB_ori_flag=(int*)malloc(sizeof(int)*(NUM_ACTIVITY+1));
        CSC2=(int*)malloc(sizeof(int)*(NTDEF_NUMSEQUENCE-1));
    
    static int UB=1000000;//#initial upper bound value
    static int BestEstimateCost=1000000;
    static bool SolutionFoundFlag=0;
    static int* CSCsol;
    static int* CSCbestestimate;
    char FORFILE[NTDEF_MAXSTRSIZE];
    if(CSCsol==NULL)CSCsol=(int*)malloc(sizeof(int)*(NTDEF_NUMSEQUENCE-1));
    if(CSCbestestimate==NULL)CSCbestestimate=(int*)malloc(sizeof(int)*(NTDEF_NUMSEQUENCE-1));
    sprintf(FORFILE,"CCost=%d CSequence=%d UB=%d EstCost=%d (%f) ",Cc,tc,UB,EstTotalCost,(float)NTN_Ticc());fputs(FORFILE, FH);
    for(int fp=0;fp<(NTDEF_NUMSEQUENCE-1);fp++){sprintf(FORFILE, "%d ",CSC[fp]);fputs(FORFILE, FH);}fputs("\n", FH);

    int EstimatedCostPartial=EstTotalCost+(NTDEF_NUMSEQUENCE-1-tc)*40;
    if(tc>=(NTDEF_NUMSEQUENCE-1))
    {
        //calc total Cc+goal
        printf("Solution part: ");for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)printf("%d ",CSC[f]);printf("\n");
        int Ccc=NTLBCost_discreteActivityTEST(CSC, Xc);
        if(Ccc<UB)
        {
            UB=Ccc;
            SolutionFoundFlag=1;
            for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)
                CSCsol[f]=CSC[f];
            fputs("\t\tSolution ", FH);
            for(int fp=0;fp<(NTDEF_NUMSEQUENCE-1);fp++){sprintf(FORFILE, "%d ",CSC[fp]);fputs(FORFILE, FH);}
            sprintf(FORFILE,"UB= %d (%fs)", UB,NTN_Ticc());fputs(FORFILE, FH);fputs("\n", FH);
            
            //2nd round checking by omitting each activity of the sequence
            int CSCc2[NTDEF_MAXSTRSIZE];
            bool GotSomethingChangedFlag=NTDEF_PART_A_TEST;
            //Part A test:
            
            while (GotSomethingChangedFlag)
            {
                GotSomethingChangedFlag=0;
                for(int ff=0;ff<(NTDEF_NUMSEQUENCE-1);ff++)
                {
                    for(int ff2=0;ff2<(NTDEF_NUMSEQUENCE-1);ff2++)CSCc2[ff2]=CSC[ff2];
                    CSCc2[ff]=-1;
                    int Xcc2[NTDEF_MAXSTRSIZE];
                    for(int fff=0;fff<NUM_VARIABLE;fff++)Xcc2[fff]=VARIABLE_LIST[fff].val;
                    int NewCost=NTL_2ndCSCCheck(CSCc2, Xcc2); //NTLBCost_discreteActivity(CSCc2, Xc);
                    if(NewCost<UB)
                    {
                        UB=NewCost;GotSomethingChangedFlag=1;
                        for(int ff2=0;ff2<(NTDEF_NUMSEQUENCE-1);ff2++)CSC[ff2]=CSCc2[ff2];
                        fputs("\t\tNew Solution ", FH);
                        for(int fp=0;fp<(NTDEF_NUMSEQUENCE-1);fp++){sprintf(FORFILE, "%d ",CSC[fp]);fputs(FORFILE, FH);}
                        sprintf(FORFILE,"UB= %d (%fs)", UB,NTN_Ticc());fputs(FORFILE, FH);fputs("\n", FH);
                    }
                }
            }
            
        }
        if(EstimatedCostPartial<BestEstimateCost)// && SolutionFoundFlag==0)
        {
            BestEstimateCost=EstimatedCostPartial;
            for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)
                CSCbestestimate[f]=CSC[f];
            fputs("\t\tBest Partial Solution ", FH);
            for(int fp=0;fp<(NTDEF_NUMSEQUENCE-1);fp++){sprintf(FORFILE, "%d ",CSCbestestimate[fp]);fputs(FORFILE, FH);}
            sprintf(FORFILE,"B_Esti= %d", BestEstimateCost);fputs(FORFILE, FH);fputs("\n", FH);
        }
        return;
    }
    else if(EstimatedCostPartial<BestEstimateCost)// && SolutionFoundFlag==0)
    {
        BestEstimateCost=EstimatedCostPartial;
        for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)
            CSCbestestimate[f]=CSC[f];
        fputs("\t\tBest Partial Solution ", FH);
        for(int fp=0;fp<(NTDEF_NUMSEQUENCE-1);fp++){sprintf(FORFILE, "%d ",CSCbestestimate[fp]);fputs(FORFILE, FH);}
        sprintf(FORFILE,"B_Esti= %d", BestEstimateCost);fputs(FORFILE, FH);fputs("\n", FH);
    }
    
    //#stopflag mechanism
    if(STOPFLAG==0)
    {
        float timelapse=NTN_Ticc();
        if(timelapse>60)STOPFLAG=1;
    }
    else printf("TIME TO STOP!! (%f)\n",NTN_Ticc());
    
    
    for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)
        CSC2[f]=CSC[f];
    
    //LB evaluation
    for(int f=0;f<NUM_ACTIVITY;f++)
    {
        bool PreconFlag;
        if(ACTIVITY_LIST[f].precon_num!=0)
            PreconFlag=NT_checkpreconholdsornot(Xc, f);
        else PreconFlag=1;
        if(PreconFlag==1)
        {
            NT_manipstatefromacteffect(Xc, State1, f);
            LB_ori[f]=Jmemetic(NUM_ACTIVITY, NTDEF_NUMSEQUENCE-1, NTDEF_NUMSEQUENCE-2-tc, State1, LOCALINVALID2OPT, NUM_INVALIDLOCAL)+ACTIVITY_LIST[f].Weight+Cc;
        }
        else LB_ori[f]=1000000;
    }
    LB_ori[NUM_ACTIVITY]=Jmemetic(NUM_ACTIVITY,NTDEF_NUMSEQUENCE-1,NTDEF_NUMSEQUENCE-2-tc,Xc,LOCALINVALID2OPT,NUM_INVALIDLOCAL)+NTDEF_NOOPWEIGHT+Cc;
    
    
    if(tc!=0)
    {
        if(NTDEF_PART_B_TEST)
        {
            //Check for repeat activity (A.A=A) and local inconsistency
            for(int f=0;f<NUM_INVALIDLOCAL;f++)
                if(CSC[tc-1]==LOCALINVALID2OPT[0][f])
                    LB_ori[LOCALINVALID2OPT[1][f]]=1000000;
        }
        
        
        
        //Check for redundant activity
        for(int f=0;f<NUM_ACTIVITY;f++)
        {
            bool RedundantF=NTL_IsActivityRedundant(Xc, f);
            if(RedundantF==1)LB_ori[f]=1000000;
        }
        
        //set all subsequent activity of -1 to be -1
        if(CSC[tc-1]==-1)
            for(int f=0;f<NUM_ACTIVITY;f++)
                LB_ori[f]=1000000;
    }
    
    
    for(int f=0;f<(NUM_ACTIVITY+1);f++)
        LB_sort[f]=LB_ori[f];
    qsort(LB_sort, NUM_ACTIVITY+1, sizeof(int), NT_cmpfunc);//sort
    for(int f=0;f<(NUM_ACTIVITY+1);f++)
        LB_ori_flag[f]=0;
    for(int f=0;f<(NUM_ACTIVITY+1);f++)
    {
        int vall=LB_sort[f];
        int findex;
        for(findex=0;findex<(NUM_ACTIVITY+1);findex++)
            if(LB_ori[findex]==vall && LB_ori_flag[findex]==0)
            {
                LB_ori_flag[findex]=1;
                LB_sort_Act[f]=findex;
                break;
            }
    }
    
    
    //recursion
    int Tn=tc+1;
    for(int f=0;f<(NUM_ACTIVITY+1);f++)
    {
        int Cn;
        if(LB_sort[f]>=UB || LB_sort[f]>=1000000)break;//Very important part
        if(LB_sort_Act[f]!=NUM_ACTIVITY)
        {
            Cn=Cc+ACTIVITY_LIST[LB_sort_Act[f]].Weight;
            NT_manipstatefromacteffect(Xc, State1, LB_sort_Act[f]);
            CSC2[tc]=LB_sort_Act[f];
        }
        else
        {
            Cn=Cc+NTDEF_NOOPWEIGHT;
            CSC2[tc]=-1;//equal Num_activity noop
            for(int f2=0;f2<NUM_VARIABLE;f2++)
                State1[f2]=Xc[f2];
        }
        NT_BnB(Cn, Tn, State1, CSC2,LB_sort[f]);
    }
    free(State1);free(LB_ori);free(LB_sort);free(LB_sort_Act);free(LB_ori_flag);free(CSC2);
    
     //#handle act=-1 too
    //#remember to copy CSC before use as it is referenced by pointer
    //make sure recursive sequence is correct
    //space complexity or time complexity?
    //additional weight from memetic -1 -1 -1 need to be cancelled
    if(tc==0)FinalUB=UB;
    
}


//Janos part after this//////////////////
FILE *ParamFile;

int NumberOfGenerations,
NumberOfBacteria,
NumberOfClones,
MutationSegmentLength,
NumberOfInfections,
InfectionSegmentLength;

intVECTOR EvalOfPopulation,
EvalOfClones,
OrderBacteria,
TempBacterium,
rndPerm,
PermPos;

intMATRIX Population,
Clones;

int cost(intVECTOR Act,int initState[])
{
//    int Act2[NTDEF_NUMSEQUENCE-1];
//    for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)
//        Act2[f]=Act[f];
    int cst=NTLBCost_discreteActivity(Act ,initState);
    return cst;
}


/* Allocate space for vector of int cells for one dimensional dynamic intvector[cols] */
void intVectorAllocate(intVECTOR *intvector, int nCols)
{
    if ((*intvector = (intVECTOR) calloc(nCols, sizeof(int))) == NULL)
    {
        fprintf(stderr, "Sorry! Not enough memory\n");
        exit(1);
    }
}

/* Allocate space for columns (int cells) for dynamic two dimensional intmatrix[rows][cols] */
void intAllocateCols(intVECTOR intmatrix[], int nRows, int nCols)
{
    int  i;
    
    for (i = 0;  i < nRows;  i++)
        intVectorAllocate(&intmatrix[i], nCols);
}

/* Allocate space for a two dimensional dynamic intmatrix [rows] [cols] */
void intMatrixAllocate(intMATRIX *intpmatrix, int nRows, int nCols)
{
    if ( (*intpmatrix  =  (intMATRIX) calloc(nRows,  sizeof(intVECTOR) ) )   ==  NULL)
    {
        fprintf(stderr, "Sorry! Not enough memory\n");
        exit(1);
    }
    
    intAllocateCols(*intpmatrix, nRows, nCols);
}

/* free space for two dimensional (int) dynamic array */
void intMatrixFree(intMATRIX intmatrix,  int nRows)
{
    int   i;
    for (i = 0;  i < nRows;  i++)
        free(intmatrix[i]);
    free(intmatrix);
}

/* generating a random integer between n and m */

int RandomValue(int n, int m)
{
    int rnd;
    
    rnd=rand()%(m-n+1)+n;
    return(rnd);
}

/* create RandomValue permutation */

void RandomValuePermutation(int length)
{
    int swap,
    swapPosition,
    i;
    
    for (i=0;i<length;i++)
        rndPerm[i]=i;
    for (i=0;i<length-1;i++)
    {
        swap=rndPerm[i];
        swapPosition=RandomValue(i,length-1);
        rndPerm[i]=rndPerm[swapPosition];
        rndPerm[swapPosition]=swap;
    }
}


/* read the params.txt file the get the parameters for Bacterial Memetic Algorithm */
void ReadParamFile()
{
    
    // open file containing the parameters
    if((ParamFile = fopen("params.txt","r")) ==NULL)
    {
        fprintf(stderr, "Cannot open parameter file!\n");
        exit(-1);
    }
    
    // read parameters from the parameter file
    fscanf(ParamFile, "%*s%*s%*s%d\n", &NumberOfGenerations);
    fscanf(ParamFile, "%*s%*s%*s%d\n", &NumberOfBacteria);
    fscanf(ParamFile, "%*s%*s%*s%d\n", &NumberOfClones);
    fscanf(ParamFile, "%*s%*s%*s%d\n", &MutationSegmentLength);
    fscanf(ParamFile, "%*s%*s%*s%d\n", &NumberOfInfections);
    fscanf(ParamFile, "%*s%*s%*s%d\n", &InfectionSegmentLength);
    
    fclose(ParamFile);
    
}

// bacterial mutation operator of BMA
void BacterialMutation(int bacteriumID, int NoA, int TS, int CS, int varS[])
{
    int clones,
    cloneID,
    i,
    NSegment,
    segment,
    minEval;
    
    
    // create clones
    for (clones=0;clones<NumberOfClones+1;clones++)
        for (i=0;i<CS;i++)
            Clones[clones][i]=Population[bacteriumID][i];
    
    RandomValuePermutation(CS);
    NSegment=CS/MutationSegmentLength;
    
    
    for (segment=0;segment<NSegment;segment++)
    {
        for (i=0;i<MutationSegmentLength;i++)
        {
            PermPos[i]=rndPerm[segment*MutationSegmentLength+i];
        }
        
        // mutation of the clones
        for (clones=1;clones<NumberOfClones+1;clones++)
        {
            for (i=0;i<MutationSegmentLength;i++)
            {
                Clones[clones][PermPos[i]]=RandomValue(-1,NoA-1);
            }
        }
        
        // evaluate the clones
        for (clones=0;clones<NumberOfClones+1;clones++)
        {
            for(i=0;i<CS;i++)
            {
                TempBacterium[i]=Clones[clones][i];
            }
            for(i=CS;i<TS;i++)
            {
                TempBacterium[i]=-1;
            }
            EvalOfClones[clones]=cost(TempBacterium,varS);
        }
        
        // selection of the best clone
        minEval=EvalOfClones[0];
        cloneID=0;
        for (clones=1;clones<NumberOfClones+1;clones++)
        {
            if (EvalOfClones[clones]<minEval)
            {
                minEval=EvalOfClones[clones];
                cloneID=clones;
            }
        }
        
        
        // best clone transfers the mutated part to other clones
        for (clones=0;clones<NumberOfClones+1;clones++)
            for (i=0;i<CS;i++)
            {
                if(clones!=cloneID)
                    Clones[clones][i]=Clones[cloneID][i];
            }
    }
    
    // use the best clone as new bacterium
    for (i=0;i<CS;i++)
        Population[bacteriumID][i]=Clones[0][i];
}

/* ordering of the population */

void OrderPopulation(int TS, int CS, int varS[])
{
    int ind,
    indID,
    i,
    maxEval;
    
    // evaluate the bacteria
    for (ind=0;ind<NumberOfBacteria;ind++)
    {
        for(i=0;i<CS;i++)
        {
            TempBacterium[i]=Population[ind][i];
        }
        for(i=CS;i<TS;i++)
        {
            TempBacterium[i]=-1;
        }
        
        EvalOfPopulation[ind]=cost(TempBacterium,varS);
    }
    
    // order the population according to the evaluation
    for (ind=0;ind<NumberOfBacteria;ind++)
    {
        maxEval=EvalOfPopulation[0];
        indID=0;
        for (i=1;i<NumberOfBacteria;i++)
        {
            if (EvalOfPopulation[i]>maxEval)
            {
                maxEval=EvalOfPopulation[i];
                indID=i;
            }
        }
        EvalOfPopulation[indID]=-1;
        OrderBacteria[NumberOfBacteria-ind-1]=indID;
    }
}

/* gene transfer operator of BMA */

void GeneTransfer(int TS, int CS, int varS[])
{
    int inf,
    i,
    sourceBacterium,
    destBacterium,
    GenePosition;
    
    for (inf=0;inf<NumberOfInfections;inf++)
    {
        OrderPopulation(TS,CS,varS);
        sourceBacterium=RandomValue(0,NumberOfBacteria/2-1);
        destBacterium=RandomValue(NumberOfBacteria/2,NumberOfBacteria-1);
        if((CS-InfectionSegmentLength)>0){
        GenePosition=RandomValue(0,CS-InfectionSegmentLength);
        for (i=0;i<InfectionSegmentLength;i++)
        {
            Population[OrderBacteria[destBacterium]][GenePosition+i]=Population[OrderBacteria[sourceBacterium]][GenePosition+i];
        }}
    }
}

int Jmemetic(int NumberOfActivities, int TotalSequence, int CurrentSequence, int S[], intMATRIX LUT, int size)
{
    int i,j,
    ind,
    pos,
    gen,
    found,
    conflicting,
    minEval = 0,
    minEvalID;
    
    // allocate space for dynamic variables
    intMatrixAllocate(&Population,NumberOfBacteria,TotalSequence);
    intMatrixAllocate(&Clones,NumberOfClones+1,TotalSequence);
    intVectorAllocate(&EvalOfPopulation,NumberOfBacteria);
    intVectorAllocate(&EvalOfClones,NumberOfClones+1);
    intVectorAllocate(&OrderBacteria,NumberOfBacteria);
    intVectorAllocate(&rndPerm,TotalSequence);
    intVectorAllocate(&PermPos,MutationSegmentLength);
    intVectorAllocate(&TempBacterium,TotalSequence);
    
    // create initial population
    for (i=0;i<NumberOfBacteria;i++)
    {
        for(j=0;j<CurrentSequence;j++)
        {
            Population[i][j]=RandomValue(-1,NumberOfActivities-1);
        }
    }
    
    // starting the evolutionary process
    for (gen=0;gen<NumberOfGenerations;gen++)
    {

        //printf("Generation: %d\n",gen+1);
        
        // bacterial mutation operator for each bacteria
        for (ind=0;ind<NumberOfBacteria;ind++)
        {
            BacterialMutation(ind,NumberOfActivities,TotalSequence,CurrentSequence,S);//#check
        }
        
        
        //gene transfer operator for the population
        GeneTransfer(TotalSequence,CurrentSequence,S);

        
        // reparation of the individuals based on the lookup table
        for (ind=0;ind<NumberOfBacteria;ind++)
        {
            for(pos=0;pos<CurrentSequence-1;pos++)
            {
                found=0;
                for(i=0;i<size;i++)
                {
                    if((LUT[0][i]==Population[ind][pos])&&(LUT[1][i]==Population[ind][pos+1])) found=1;
                }
                if (found==1)
                {
                    // conflict is found, thus a new random nonconflicting value is generated
                    do
                    {
                        Population[ind][pos+1]=RandomValue(-1,NumberOfActivities-1);
                        conflicting=0;
                        for(i=0;i<size;i++)
                        {
                            if((LUT[0][i]==Population[ind][pos])&&(LUT[1][i]==Population[ind][pos+1])) conflicting=1;
                        }
                    }
                    while(conflicting==1);
                }
            }
        }
        
        // evaluate the bacteria
        for (ind=0;ind<NumberOfBacteria;ind++)
        {
            for(i=0;i<CurrentSequence;i++)
            {
                TempBacterium[i]=Population[ind][i];
            }
            for(i=CurrentSequence;i<TotalSequence;i++)
            {
                TempBacterium[i]=-1;
            }
            
            EvalOfPopulation[ind]=cost(TempBacterium,S);
        }
        
        // selection of the best bacterium
        minEval=EvalOfPopulation[0];
        minEvalID=0;
        for (i=1;i<NumberOfBacteria;i++)
        {
            if (EvalOfPopulation[i]<minEval)
            {
                minEval=EvalOfPopulation[i];
                minEvalID=i;
            }
        }
        //printf("Best bacterium: %d\n",minEval);
    }
    
    // free space of dynamic variables
    intMatrixFree(Population,NumberOfBacteria);
    intMatrixFree(Clones,NumberOfClones+1);
    free(EvalOfPopulation);
    free(EvalOfClones);
    free(OrderBacteria);
    free(rndPerm);
    free(PermPos);
    return minEval-(TotalSequence-CurrentSequence)*NTDEF_NOOPWEIGHT;
}


void NTProgLoop()
{
    Ticc('i');
    srand((unsigned int)time(NULL));
    rand();
    rand();
    NTgenVariablenActivityfromFile();
    ReadParamFile();
    int Xc[NTDEF_MAXSTRSIZEm],CSC[NTDEF_MAXSTRSIZEm];
    int Cc=0,tc=0;
    for(int f=0;f<NUM_VARIABLE;f++)Xc[f]=VARIABLE_LIST[f].val;
    for(int f=0;f<(NTDEF_NUMSEQUENCE-1);f++)CSC[f]=-10;
    NTN_Ticc();STOPFLAG=0;
    
    
//    //int CSCtest[]={34,26,-1 ,29, 22, -1, -1, -1, 0, 14};
//    int CSCtest[]={34, 26, 24, 17, 21, 2, 4, 3, 0, 14};
//    int Ccc=NTL_2ndCSCCheck(CSCtest, Xc);
//    int Ccc2=NTLBCost_discreteActivityTEST(CSCtest, Xc);
//    printf("Result= %d %d\n",Ccc,Ccc2);return;
//    
//    if(NTDEF_PART_C_TEST!=1)NUM_INVALIDLOCAL=0;

    NT_BnB(Cc, tc, Xc, CSC,1000000);
    Ticc('o');printf("Final UB %d",FinalUB);
}

