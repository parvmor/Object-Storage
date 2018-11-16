#!/usr/bin/env bash

if [ -d test/keyval ]; then
    rm -rf test/keyval;
fi
mkdir -p test/keyval

n_proc=${1}
echo "Running $(( ${n_proc} + 1 )) processes with ${2} and ${3}..."
make clean
make cache=${2} dbg=${3}
dd if=/dev/zero of=disk.img bs=1M count=2048
./objfs mnt1 -o use_ino
rand_put parv > test/keyval/keyparv

for i in `seq 0 ${n_proc}`; do
    rand_put ${i} > test/keyval/key${i} &
    pids1[${i}]=$!
done

for pid in ${pids1[*]}; do
    wait ${pid}
done

for i in `seq 0 ${n_proc}`; do
    rand_get ${i} > test/keyval/val${i} &
    pids2[${i}]=$!
done

for pid in ${pids2[*]}; do
    wait ${pid}
done

for i in `seq 0 ${n_proc}`; do
    diff test/keyval/key${i} test/keyval/val${i} 1>/dev/null
    if [ ! $? -eq 0 ]; then
        echo "Failed on ${i}"
        exit 1
    fi
done

fusermount -u mnt1
