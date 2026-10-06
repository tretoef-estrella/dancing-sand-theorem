# usage: zsh scratch/zoom.sh PAGE NAME Y0frac Y1frac  -> 200 dpi crop of page between fractions of height
P=$1; N=$2; Y0=$3; Y1=$4
H=2339; W=1653
y=$(( H*Y0/100 )); h=$(( H*(Y1-Y0)/100 ))
pdftoppm -r 200 -png -f $P -l $P -x 0 -y $y -W $W -H $h material/paper/THE_DANCING_SAND_THEOREM_v6.pdf scratch/png200/$N
