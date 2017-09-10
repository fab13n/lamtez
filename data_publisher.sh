L=./lamtez
T=tezos-client
D=michelson

make $L

set -x

# Get a crypto identity and some tz to play with
if $T list known identities | grep -q ^myself: ; then
	echo "Already have an account"
else
    $T gen keys myself
fi
# Need some money
if $T list known contracts | grep -q ^mymoney: ; then
	echo "Already have money"
else
	$T originate free account mymoney for myself
fi

MYKEY=$($T list known identities|grep ^myself: | cut -d' ' -f2)
if [ -z "$T" ]; then echo "Identity/key not found"; exit 1; fi

I=contracts/data_publisher
O=$D/$(basename $I)
INITIAL_STORE='@key = '$MYKEY' @data="O Captain! my Captain! our fearful trip is done" @fee=tz1.00'

# Compile the contract and associated data
$L --file $I.ltz \
   --output $O.tz \
   --store-string "$INITIAL_STORE" \
   --store-output $O.data  \
   --parameter "None" \
   --parameter-output $O.0.param \
   || exit 2

# Run it alone to test
$T run program file:$O.tz \
   on storage "$(cat $O.data)" \
   and input "$(cat $O.0.param)" \
   -amount 1 \
   || exit 3

# Sign a new text
NEW_TEXT="The ship has weathered every rack, the prize we sought is won"
NEW_TEXT_SIG=$($T hash and sign data "\"$NEW_TEXT\"" for myself | grep ^Signature: | cut -d'"' -f2)

# Compile a new parameter updating the publisher with this signed text
$L $I.ltz \
   --parameter "Some(sig:$NEW_TEXT_SIG, \"$NEW_TEXT\")"\
   --parameter-output $O.1.param \
   || exit 4

# Run program with updating parameter
$T run program file:$O.tz \
   on storage "$(cat $O.data)" \
   and input "$(cat $O.1.param)" \
   -amount 1 \
   || exit 5

# Commit/Replace into Tezos
if $T list known contracts | grep -q ^data_publisher: ; then
	$T forget contract data_publisher
fi
$T originate contract data_publisher \
   for myself \
   transferring 10 from mymoney \
   running file:$O.tz -init "$(cat $O.data)" \
   || exit 6

# Change the published data on the blockchain; first create the parameter:
NEW_TEXT="The port is near, the bells I hear, the people all exulting"
NEW_TEXT_SIG=$($T hash and sign data "\"$NEW_TEXT\"" for myself | grep ^Signature: | cut -d'"' -f2)
$L $I.ltz \
   --parameter "Some(sig:$NEW_TEXT_SIG, \"$NEW_TEXT\")"\
   --parameter-output $O.2.param \
   || exit 7

# Then send it through a transfer
$T transfer 1 from mymoney to data_publisher -arg "$(cat $O.2.param)" || exit 8

# Now, check the blockchain at https://fredcy.github.io/tezos-client/#/operations
