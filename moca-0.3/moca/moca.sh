#!/bin/bash
tempI=`mktemp _tempmoca_XXXXXXXX.smt2`
tempO=`mktemp _tempmoca_XXXXXXXX.txt`
timeout 59 moca $1 -tmpi=`basename $tempI` -tmpo=`basename $tempO` ${@:2}
rm -f `basename $tempI`
rm -f `basename $tempO`
