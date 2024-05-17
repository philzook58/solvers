#!/bin/sh
#-----------
# File:      nanocopi.sh
# Version:   2.0
# Date:      1 May 2021
#-----------
# Purpose:   Invokes the nanoCoP-i prover
# Usage:     ./nanocopi.sh <problem file> [<time limit>]
# Author:    Jens Otten
# Web:       www.leancop.de/nanocop-i/
# Copyright: (c) 2017-2021 by Jens Otten
# License:   GNU General Public License
#-----------

#-----------
# Parameters

# set the nanoCoP-i prover path
PROVER_PATH=/home/philip/Documents/solvers/nanoCoP-i20

# set Prolog system (ECLiPSe 5.x or SWI), path and options

#PROLOG=eclipse
#PROLOG_PATH=/usr/bin/eclipse
#PROLOG_OPTIONS='-e'

PROLOG=swi
PROLOG_PATH=/usr/bin/swipl
#PROLOG_OPTIONS='-O -L120M -G120M -T100M -q -g'
PROLOG_OPTIONS='--debug=false -O -q -g'

# print proof [yes|no]
PRINT_PROOF=yes
# save proof [yes|no]
SAVE_PROOF=no
# proof layout [compact|connect|leantptp|readable]
PROOF_LAYOUT=leantptp

# set TPTP library path
# export TPTP=.

#----------
# Functions

nanocopi()
{
# Input: $SET, $COMP, $TIME_PC
  TLIMIT=`expr $TIME_PC '*' $TIMELIMIT / 111 + 1`
  $PROLOG_PATH $PROLOG_OPTIONS \
  "assert(prolog('$PROLOG')), assert(proof('$PROOF_LAYOUT')), ['$PROVER_PATH/nanocopi_main.pl'], nanocopi_main('$FILE',$SET,_), halt." \
   > $OUTPUT &
  PID=$!
  CPU_SEC=0
  trap "rm $OUTPUT; kill $PID >/dev/null 2>&1; exit 2"\
   ALRM XCPU INT QUIT TERM
  while [ $CPU_SEC -lt $TLIMIT ]
  do
    sleep 1
    CPUTIME=`ps -p $PID -o time | grep :`
    if [ ! -n "$CPUTIME" ]; then break; fi
    CPU_H=`expr 1\`echo $CPUTIME | cut -d':' -f1\` - 100`
    CPU_M=`expr 1\`echo $CPUTIME | cut -d':' -f2\` - 100`
    CPU_S=`expr 1\`echo $CPUTIME | cut -d':' -f3\` - 100`
    CPU_SEC=`expr 3600 '*' $CPU_H + 60 '*' $CPU_M + $CPU_S`
  done
  if [ -n "$CPUTIME" ]
  then rm $OUTPUT; kill $PID >/dev/null 2>&1
  else
    RESULT1=`egrep ' Theorem| Unsatisfiable' $OUTPUT`
    RESULT2=`egrep ' Non-Theorem| Satisfiable' $OUTPUT`
    if [ $COMP = n ]; then RESULT2= ; fi
    if [ -n "$RESULT1" -o -n "$RESULT2" ]
    then
      if [ $PRINT_PROOF = yes ]; then cat $OUTPUT
      else if [ -n "$RESULT1" ]; then echo $RESULT1
           else echo $RESULT2; fi
      fi
      if [ $SAVE_PROOF = yes ]; then mv $OUTPUT $PROOF_FILE
      else rm $OUTPUT; fi
      if [ -n "$RESULT1" ]; then exit 0; else exit 1; fi
    else rm $OUTPUT
    fi
  fi
}

#-------------
# Main Program

if [ $# -eq 0 -o $# -gt 2 ]; then
 echo "Usage: $0 <problem file> [<time limit>]"
 exit 2
fi

if [ ! -r "$1" ]; then
 echo "Error: File $1 not found" >&2
 exit 2
fi

if [ -n "`echo "$2" | grep '[^0-9]'`" ]; then
 echo "Error: Time $2 is not a number" >&2
 exit 2
fi

if [ $# -eq 1 ]
 then TIMELIMIT=100
 else TIMELIMIT=$2
fi

FILE=$1
PROOF_FILE=$FILE.proof
OUTPUT=TMP_OUTPUT_nanocopi_`date +%F_%T_%N`

set +m

# invoke nanoCoP-i core prover with different settings SET
# for time TIME_PC [%]; COMP=y iff settings are complete

SET="[cut,comp(6)]";           COMP=y; TIME_PC=15; nanocopi
SET="[scut]";                  COMP=n; TIME_PC=10; nanocopi
SET="[scut,cut]";              COMP=n; TIME_PC=5;  nanocopi
SET="[noeq,scut]";             COMP=n; TIME_PC=5;  nanocopi
SET="[reo(20),conj,cut]";      COMP=n; TIME_PC=10; nanocopi
SET="[reo(22),conj,cut]";      COMP=n; TIME_PC=10; nanocopi
SET="[reo(33),conj,scut,cut]"; COMP=n; TIME_PC=10; nanocopi
SET="[reo(2),cut]";            COMP=n; TIME_PC=10; nanocopi
SET="[reo(5),cut]";            COMP=n; TIME_PC=10; nanocopi
SET="[reo(6),scut]";           COMP=n; TIME_PC=5;  nanocopi
SET="[noeq,reo(64),cut]"       COMP=n; TIME_PC=5;  nanocopi
SET="[]";                      COMP=y; TIME_PC=99; nanocopi

echo Timeout
exit 2

