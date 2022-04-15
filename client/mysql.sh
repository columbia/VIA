#!/bin/bash
#--table-size=10000 \

SRV=$1
REPTS=${2-10}

for i in `seq 1 $REPTS`; do
sysbench \
        --db-driver=mysql \
        --mysql-user=sbtest \
        --mysql_password=kvm \
        --mysql-db=sbtest \
        --mysql-host=$SRV \
        --mysql-port=3306 \
        --tables=10 \
        --table-size=500 \
        --threads=16 \
        --report-interval=2 \
        --mysql-ssl \
        /usr/share/sysbench/oltp_read_write.lua run | tee \
        >(grep 'transactions:' | awk '{ print $3 }' | sed 's/^(\(.*\)/\1/' >> mysql.txt)
done;

