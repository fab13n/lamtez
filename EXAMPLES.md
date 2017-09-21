# Some examples inspired by www.michelson-lang.com

As a comparison with hand-written Michelson code, here are some
examples of contracts, described on http://www.michelson-lang.com,
rewritten in Lamtez.

## Identity

This one is as striaghtforward in Lamtez as in Michelson: just take a
unit and return it.

    # id.ltz
    fun p :: unit: p

## Take my money

Here again nothing fancy:

    fun k :: key:
      let contract = contract-get k;
      contract-call contract () tz1.00

## At least

Here we'll use a sum case matching to encode an if/then/else. We also
introduce a stored variable `minimum`:

    @minimum :: tez = tz1.00 # with a default value
    fun p :: unit: if self-amount < @minimum: fail; | else: () end

## Queue

This one works exactly as the Michelson version (we only declare a
type alias for the elements in the queue, so that it's easily
changed). As you can see, options are handled like other sum types
with a `?...|...|...` accessor.

    type data = string

    @i   :: nat = 0
    @j   :: nat = 0
    @map :: map nat data = map-empty

    fun parameter :: option data:
    case parameter
    | Some data: @map <- map-update @j (Some data) @map;
                 @j <- @j + 1;
                 None
    | None: case map-get @i @map
            | None: None
            | Some data: @map <- map-update @i None @map;
                         @i <- @i + 1;
                         Some data
            end
    end

## Data publisher

There are no new concept introduced here. I've made the fee a stored
parameter, because it's not harder than keeping it hard-coded.
Compared to other ML dialects, this example shows that Lamtez still
lacks destructuring (irrefutable) patterns: instead of writing
`Some signed_data: let sig = signed_data.0; let data = signed_data.1; ...`
it would have been nice to write `Some (sig, data): ...`.

    type data = string
    type operation = option (sig * data)

    @key  :: key
    @data :: data
    @fee  :: tez

    fun parameter :: operation:
    case parameter
    | None: case self-amount >= @fee
            | False: fail
            | True:  @data
			end
    | Some signed_data: let sig  = signed_data.0;
                        let data = signed_data.1;
                        case crypto-check @key sig data
                        | False: fail
                        | True: @data <- data; data
						end
    end

## User accounts

Nothing special about this contract either; it's made more readable than its
Michelson counterpart thanks to named operations and operation fields, and
thanks to the store update operations separated from result computation.

    type withdrawal = Key: key * Amount: tez * Signature: signature
    type operation = Deposit key + Withdrawal withdrawal

    @accounts :: map key tez

    fun operation :: operation:
    case operation
    | Deposit key:
        let new_balance = case map-get key @accounts
                          | None:         self-amount            # Create new account
                          | Some balance: self-amount + balance  # update existing account
						  end;
        @accounts <- map-update key (Some new_balance) @accounts;
        ()
    | Withdrawal w: if not crypto-check w.Key w.Signature (crypto-hash w.Amount): fail end;
                    case map-get w.Key @accounts
                    | None: fail  # withdrawal denied (no such account)
                    | Some balance:
                        if balance < w.Amount: fail end;  # withdrawal denied (insufficient funds)
                        let new_balance = case balance = w.Amount
                                          | True:  None                        # Delete empty account
                                          | False: Some (balance - w.Amount)); # update account
										  end
                        @accounts <- map-update w.Key new_balance @accounts;
                        contract-call (contract-get w.Key) () w.Amount))
					end
	end

## King of Tez

A contract that's all about updating the store (plus a very simple condition
checking).

    @royal_key         :: key
    @enthronement_date :: time
    @enthronement_cost :: tez

    fun parameter :: key:
    let one_week = 60 * 60 * 24 * 7;
    if self-now < @enthronement_date + one_week and self-amount < @enthronement_cost: fail end;
    @royal_key         <- parameter;
    @enthronement_date <- self-now;
    @enthronement_cost <- self-amount;

## Some simpler examples

    # add1
    fun p :: int: p + 1

    # concat_string
    @stored_string :: string
    fun param: @stored_string ^ param

## Lock contract

    @release_date :: time
    @amount       :: tez
    @destination  :: contract unit unit

    fun parameter :: unit:

    if self-now < @release_date: fail | else: () end;
    contract-call @destination () @amount)

## Lambda, map, and creating contracts

First, mapping a function on a list:

    fun param :: list int:
      let f = (fun x: x + 1);
      list-map f param

With the following example, something noteworthy is happening. When writing
the current contract, Lamtez handles the boilerplate related to storage access
and update. However, when a contract creates another contract, the later
doesn't benefit from those features. It is initialized with a function of type
`∀ parameter storage result: (parameter×storage) → (result×storage)`, and the
manipulation of storage fields must be performed explicitly by the function
body.

Here, within the lambda, `x` is bound to a `int×unit` pair, applies the map
operation on the first half `x.0`, then pairs the result with a unit term
`()`.


    type t = (list int * unit)

    fun param :: unit:
      let map_add1 = fun x :: t: (list-map (fun y: y+1) x.0, ());
      let key = tz1SuakBpFdG9b4twyfrSMqZzruxhpMeSrE5;
      contract-create key None False False self-amount map_add1

## Parameterizable payment contract

This one is tedious to follow in Michelson, quite a bit of stack shuffling!
With named variables and labelled types, here's my version:

    type line    = Title: string * Amount: tez * Destination: contract unit unit
    type t_param = Register: line + Execute: nat

    @approver :: contract nat (nat * bool)
    @index    :: nat
    @map      :: map nat line

    fun p :: t_param:
    case p
    | Register line: @map <- map-update @index (Some line) @map;
                     @index <- @index + 1;
                     ()
    | Execute i: let response = contract-call @approver i tz0.00;
                 (if not response.1: fail);
                 case map-get i @map
                 | None: fail  # This should not happen
                 | Some line: @map <- map-update i None @map;
                              contract-call line.Destination () line.Amount
                 end
	end

My `tz0.02` about this contract:

* my guess is, the approving contract returns the index number because
  it would be too much hassle to give it a storage slot. Having that
  automated out, we could do it. The approver signature would then
  become `nat->bool`.

* when registering a line, the index number is allocated by the
  contract, and not returned to the caller. I'm not sure how the
  approver could decide anything with so little information, I think
  this number should be returned as the contract's result.

* the strings in the registered lines don't seem to be used. Shouldn't
  we refer to lines by their name rather than by number? This would
  imply to check their unicity, and to use them as map keys.

Here's a sketch of what this different version would look like:

    type t_param = Register: (string * account * tez) + Execute: string

    @approver :: contract nat bool
    @map      :: map string (account * tez)

    fun p :: t_param:
    case p
    | Register line: let id = line.0;
                     if map-mem id @map: fail end;
                     let entry = (line.1, line.2);
                     @map <- map-update @index (Some entry) @map;
                     ()
    | Execute id: if not (contract-call @approver id tz0.00): fail end;
                  case map-get id @map
                  | None: fail  # This should not happen
                  | Some x: @map <- map-update i None @map;
                            contract-call x.0 () x.1
	              end
	end

## Some examples from the Michelson official doc

### Reservoir

The [official Michelson
documentation](https://github.com/tezos/tezos/blob/master/src/proto/alpha/docs/language.md)
also comes with some smart contract examples. The simplest non-trivial one is
a reservoir contract (think of it as a simplified crowdfunding contract):
there's a time limit and a money limit; if the contract gets more than the
money threshold before the time threshold elapse, then the money goes to an
account; otherwise it goes to another (presumably for refunds).

    @time_threshold         :: time
    @amount_threshold       :: tez
    @when_threshold_reached :: account
    @when_too_late          :: account

    \p :: unit:

    ( if self-now > @time_threshold:
        contract-call @when_too_late () self-balance
    | self-amount > @amount_threshold:
        contract-call @when_threshold_reached () self-balance
    | else: () )

For a crowdfunding contract, we should remember who contributed what; and if
the money threshold faild to be reached within the time limit, then refunds
should be sent to the original contributors. However, this would require
a support for loops, since



### Scrutable reservoir

This contract also introduces a broker, who gets a fee whether the
fundraising succeeds or not. Also, the contract keeps a status
`"open"`, `"success"` or `"timeout"`, and keeps `tz1.00` on its balance
so that the contract isn't destroyed and the status can be checked.

    @status                 :: string
    @time_threshold         :: time
    @amount_threshold       :: tez
    @when_threshold_reached :: account
    @when_too_late          :: account
    @broker                 :: account
    @broker_fee             :: tez

    fun p :: unit:

    if
    ### If the contract is realized, don't call it again ###
    | @status != "open": fail

    ### Open after timeout: let's cancel it, pay broker, send the rest to when_too_late ###
    | self-now >= @time_threshold:
        @status <- "timeout";
        let available = self-balance - tz1.00;
        let fee = if available < @broker_fee: available | else: @broker_fee end;
        contract-call @broker () fee;
        contract-call @when_too_late () (self-balance - tz1.00)

    ### Money threshold reached before timeout ###
    | self-balance >= tz1.00 + @broker_fee + @amount_threshold:
        @status <- "success";
        contract-call @broker () @broker_fee;
        contract-call @when_threshold_reached () @amount_threshold

    ### Before timeout, not enough money yet, wait ###
    | else:
        ()
    end

### Forward contract

This is the largest contract example in the doc, and mimics a classic
non-standardized financial contract. Here's its Lamtez transcription:

    # Forward financial contract, following the sample given in
    # https://github.com/tezos/tezos/blob/master/src/proto/alpha/docs/language.md
    #
    # The contract is signed on date `D`. Through it, seller `S` pledges to sell
    # a quantity `Q` of goods to buyer `B`, at a future date `Z`, and at a price
    # `K` established when the contract is signed.
    #
    # `B` and `S` have to lock up a collateral sum `C×Q` in the contract; if
    # a stakeholder fails to fulfill their obligation, all of the money locked
    # up in the contract is sent to the other party.
    #
    # Once the contract is created (`Z`), buyer and seller have to lockup their
    # collaterals before `Z+24h`. If one of them fails to do so, the contract is
    # voided, and any money sent to the contract is sent back to the owner(s).
    #
    # When the due date elapses (`T`), `B` has to pay the full agreed price, minus
    # the collateral he already locked up, before `T+24h`. If he fails to do so,
    # all the money is forfeited to `S`.
    #
    # If `B` paid the agreed price before `T+24h`, `S` has to provide the goods
    # between `T+24h` and `T+48h`. To know whether this has been done, we expect
    # a warehouse operator `W` to be connected to the blockchain, and to report
    # good deliveries to the contract. If according to `W` the agreed quantity
    # has been delivered, the

    type parameter = Payment: string + Delivery: nat

    @Q         :: nat     # quantity agreed upon (in tons)
    @T         :: time    # delivery date
    @Z         :: time    # agreement date
    @K         :: tez     # strike price (per ton)
    @C         :: tez     # collateral (per ton)
    @B         :: account # buyer
    @S         :: account # seller
    @W         :: account # warehouse
    @paid_by_B :: tez
    @paid_by_S :: tez
    @delivered :: nat

    fun parameter :: parameter:

    let one_day = 24 * 60 * 60;

    if
    ### Between Z and Z+24h, accept collaterals from B and S ###
    | self-now  <  @Z + one_day:
        case parameter
        | Delivery _: fail  # Too early for delivery
        | Payment whom: if
                        | whom = "buyer":  @paid_by_B <- @paid_by_B + self-amount; ()
                        | whom = "seller": @paid_by_S <- @paid_by_S + self-amount; ()
                        | else: fail
						end
        end

    ### After Z+24h, if collaterals haven't been sent, cancel and refund ###
    | self-balance  <  2*@Q*@C + tz1.00:  # Refund
        contract-call @B () @paid_by_B;
        contract-call @S () @paid_by_S;
        contract-call @W () self-balance  # Destroys the account

    ### Between Z+24h and T, no interaction allowed ###
    | self-now  <  @T:
        fail

    ### Between T and T+24h, accept payment by buyer from the full strike price ###
    | self-now  <  @T + one_day:
        case parameter
        | Delivery _: fail
        | Payment whom: if whom != "buyer": fail end;
                        @paid_by_B <- @paid_by_B + self-amount;
                        if @paid_by_B > @Q * @K: fail end  # Don't accept too much
        end

    ### B failed to pay after T+24h => all the money goes to S ###
    | @paid_by_B != @Q * @K:
        contract-call @S () self-balance

    ### Between T+24h and T+48h, accept Warehouse reports ###
    | self-now  <  @T + 2*one_day:
        let sender = contract-manager (self-source :: contract unit unit);
        if sender != contract-manager @W: fail end;
        case parameter
        | Payment _: fail
        | Delivery q: @delivered <- @delivered + q;
                    # Contract realized, pay S
                    if @delivered >= @Q: contract-call @S () self-balance end
	    end

    ### S failed to deliver after T+48h => all the money goes to B ###
    | True:
        contract-call @B () self-balance  # Timeout, money goes to B
    end
