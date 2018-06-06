//
//  define.h
//  WCSP_planner1
//
//  Created by Noel Tay on 1/22/16.
//  Copyright (c) 2016 Noel Tay. All rights reserved.
//

#ifndef WCSP_planner1_define_h
#define WCSP_planner1_define_h


#define NTDEF_NUMSEQUENCE 10 //number of sequence for planning, total state sequence
#define NTDEF_REVACTWEIGHT 1 //Rev activity weight default
#define NTDEF_NOOPWEIGHT 1 //Weight for noop activity
#define NTDEF_ChangedVarCost 0 //altered variable cost

#define NTDEF_MAXSTRSIZE 500
#define NTDEF_MAXSTRSIZEm 250
#define NTDEF_MAXSTRSIZEs 50


#define NTDEF_PART_A_TEST 1
#define NTDEF_PART_B_TEST 1
#define NTDEF_PART_C_TEST 1


typedef int *intVECTOR;
typedef intVECTOR *intMATRIX;


const char* NTFile_CurrentVariableValueInit="Currentvariables.txt";
const char* NTFile_Currentactivitylist="CurrentActivityList.txt";
const char* NTFile_Currentgoallist="CurrentGoal.txt";
const char* NTFile_LOG="LOG.txt";

typedef struct node5{
    char s[NTDEF_MAXSTRSIZE];
}NTSTRCT_STRING;

typedef struct node1{
    char Activityname[NTDEF_MAXSTRSIZEs];
    int precon_num;
    NTSTRCT_STRING* precon;
    int effect_num;
    NTSTRCT_STRING* effect_var;
    NTSTRCT_STRING* effect;
    int Weight;
}NTSTRCT_ACTIVITY;

typedef struct node2{
    char Variablename[NTDEF_MAXSTRSIZEs];
    int val;
    char sort; //i=int b=bool I=object as int
    char type; //v=var r=res d=dynamic_res
    bool Flag;
}NTSTRCT_VARIABLE;

typedef struct node3{
    char Variablename[NTDEF_MAXSTRSIZEs];
    int val;
    char sort; //i=int b=bool I=object as int
    char relation[10];//variablename relation val b=5 b<3
    char condition[NTDEF_MAXSTRSIZE];
    int Weight;
    bool Flag;
}NTSTRCT_ACTYREV;

typedef struct node4{
    char Goal[NTDEF_MAXSTRSIZE];
    int Weight;
}NTSTRCT_GOAL;




#endif
