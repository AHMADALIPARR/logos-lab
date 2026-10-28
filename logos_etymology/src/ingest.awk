# POSIX awk: TSV columns id,language,word,etymology,source
# This is an exact orthographic slice, NOT a morphological segmentation.
BEGIN { FS="\t"; OFS="\t" }
NR==1 { next }
NF<5 { next }
{
 id=$1; lang=$2; word=$3; etym=$4; source=$5
 if(id !~ /^[A-Za-z0-9_]+$/ || lang !~ /^[A-Za-z0-9_]+$/ || source !~ /^[A-Za-z0-9_]+$/) next
 printf "lexeme(%s,%s,",id,lang; atom(word); printf ").\n"
 printf "etymology_text(%s,",id; atom(etym); printf ",%s).\n",source
 n=length(word)
 for(i=1;i<=n;i++) { printf "orthographic_slice(%s,%d,",id,i; atom(substr(word,i,1)); printf ").\n" }
}
function atom(s, t) { t=s; gsub(/\\/,"\\\\",t); gsub(/\047/,"\047\047",t); printf "\047%s\047",t }
