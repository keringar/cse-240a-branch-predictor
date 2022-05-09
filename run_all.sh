#!/bin/sh
cd src
make all

for filename in ../traces/*
do
  echo "--- Misprediction Rates ($filename) ---"
  echo -n "static: "
  bunzip2 -kc $filename | ./predictor --static | awk 'FNR == 3 {print $3}'
  echo -n "gshare: "
  bunzip2 -kc $filename | ./predictor --gshare | awk 'FNR == 3 {print $3}'
  echo -n "tournament: "
  bunzip2 -kc $filename | ./predictor --tournament | awk 'FNR == 3 {print $3}'
  echo -n "custom (TAGE): "
  bunzip2 -kc $filename | ./predictor --custom | awk 'FNR == 3 {print $3}'
done
