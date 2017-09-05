As a comparison with hand-written Michelson code, here are some examples of
contracts, described on http://www.michelson-lang.com, rewritten in Lamtez

## Identity

This one is as striaghtforward in Lamtez as in Michelson: just take a unit
and return it.

    # id.ltz
    \(p :: unit): p

## Take my money

Here again nothing fancy:

    \(k :: key):
      let contract = contract-get k;
      contract-call contract () tz1.00

## At least

Here we'll use a sum case matching to encode an if/then/else. We also introduce
a stored variable `minimum`:

    @minimum :: tez = tz1.00 # with a default value
    \(p :: unit): ( self-amount >= @minimum ?
                  | True:  ()    # Accepted
                  | False: fail  # Contract rejected
                  )

## Queue

This one works exactly as the Michelson version (we only declare a type alias for the
elements in the queue, so that it's easily changed). As you can see, options are
handled like other sum types with a `?...|...|...` accessor.

    type data = string

    @i   :: nat = 0
    @j   :: nat = 0
    @map :: map nat data = map-empty

    \(parameter :: option data):
    ( parameter ?
    | Some data: @map <- map-update @j (Some data) @map;
                 @j <- @j + 1;
                 None
    | None: ( map-get @i @map ?
            | None: None
            | Some data: @map <- map-update @i None @map;
                         @i <- @i + 1;
                         Some data
            )
    )

## Data publisher

There are no new concept introduced here. I've made the fee a stored parameter, 
because it's not harder than keeping it hard-coded. Compared to other ML dialects,
this example shows that Lamtez still lacks destructuring (irrefutable) patterns:
instead of writing 
`Some signed_data: let sig = signed_data.0; let data = signed_data.1; ...`
it would have been nice to write `Some (sig, data): ...`.

    type data = string
    type operation = option (sig * data)

    @key  :: key
    @data :: data
    @fee  :: tez

    \(parameter :: operation):
    ( parameter ?
    | None: ( self-amount >= @fee ?
            | False: fail
            | True:  @data
            )
    | Some signed_data: let sig = signed_data.0;
                        let data = signed_data.1;
                        ( crypto-check @key sig data ?
                        | False: fail
                        | True: @data <- data; data
                        )
    )

## User accounts

    type withdrawal = Key: key * Amount: tez * Signature: signature
    type operation = Deposit key + Withdrawal withdrawal

    @accounts :: map key tez

    \(operation::operation):
    ( operation ?
    | Deposit key:
        let new_balance = ( map-get key @accounts ?
                        | None: self-amount  # Create new account
                        | Some balance: self-amount + balance  # update existing account
                        );
        @accounts <- map-update key (Some new_balance) @accounts;
        ()
    | Withdrawal w: ( crypto-check w.Key w.Signature (crypto-hash w.Amount) ?
                    | False: fail  # withdrawal denied (authentication failed)
                    | True: ( map-get w.Key @accounts ?
                            | None: fail  # withdrawal denied (no such account)
                            | Some balance:
                                ( balance >= w.Amount ?
                                | False: fail  # withdrawal denied (insufficient funds)
                                | True:  let new_balance = ( balance = w.Amount ?
                                                           | True:  None  # Delete empty account
                                                           | False: Some (balance - w.Amount)  # update account
                                                           );
                                        @accounts <- map-update w.Key new_balance @accounts;
                                        contract-call (contract-get w.Key) () w.Amount
                                )
                            )
                    )
    )

If we wanted to prevent such a deep nesting of conditions, we could have used 
the fact that `fail` stops the whole contract, with idioms `let _ = (cond ? True: fail | False: ())`:

    type withdrawal = Key: key * Amount: tez * Signature: signature
    type operation = Deposit key + Withdrawal withdrawal

    @accounts :: map key tez

    \(operation::operation):
    ( operation ?
    | Deposit key:
        let new_balance = ( map-get key @accounts ?
                          | None: self-amount  # Create new account
                          | Some balance: self-amount + balance  # update existing account
                          );
        @accounts <- map-update key (Some new_balance) @accounts;
        ()
    | Withdrawal w:
      let authenticated = crypto-check w.Key w.Signature (crypto-hash w.Amount); 
      let _ = authenticated ? True: () | False: fail;
      ( map-get w.Key @accounts ?
      | None: fail  # withdrawal denied (no such account)
      | Some balance:
        let _ = balance >= w.Amount ? True: () | False: fail;
        let new_balance = ( balance = w.Amount ?
                          | True:  None  # Delete empty account
                          | False: Some (balance - w.Amount)  # update account
                          );
        @accounts <- map-update w.Key new_balance @accounts;
        contract-call (contract-get w.Key) () w.Amount
      )
    )

## King of Tez

    @royal_key         :: key
    @enthronement_date :: time
    @enthronement_cost :: tez

    \(parameter :: key):
    let one_week = 60 * 60 * 24 * 7;
    ( @enthronement_date + one_week > self.now or self-amount > @enthronement_cost ?
    | True: @royal_key <- parameter;
            @enthronement_date <- self-now;
            @enthronement_cost <- self-amount;
            ()
    | False: fail
    )

## Some simpler examples

    # add1
    \(p :: int): p + 1

    # concat_string
    @stored_string :: string
    \param: @stored_string ^ param

## Lock contract

    @release_date :: time
    @amount       :: tez
    @destination  :: contract unit unit

    \(parameter :: unit):

    ( now >= @release_date ?
    | False: fail
    | True:  contract-call @destination () @amount)

## Lambda, map, and creating contracts

First, mapping a function on a list:

    \(param :: list int):
    let f: \x: x+1;
    list-map f param

With the following example, something noteworthy is happening: although Lamtez
handles the storage for you, so you don't have to separate it from the parameter
at the beginning nor bundle it with the result at the end, this isn't true
anymore when creating contracts: these take as parameter a function of type
`forall p r s: (p*s) -> (r*s)`.

    type t = (list int * unit)

    \(param :: unit):
    let map_add1 = \(x :: t): (list-map (\y: y+1) x.0, x.1));
    let key = tz1SuakBpFdG9b4twyfrSMqZzruxhpMeSrE5;
    contract-create key None False False self-amount map_add1

## Parameterizable payment contract

This one is tedious to follow in Michelson, quite a bit of stack shuffling!
With named variables and types, here's my version:

    type line    = Title: string * Amount: tez * Destination: contract unit unit
    type t_param = Register: line + Execute: nat

    @approver :: contract nat (nat * bool)
    @index    :: nat
    @map      :: map nat line

    \(p :: t_param):
    ( p ?
    | Register line: @map <- map-update @index (Some line) @map;
                     @index <- @index + 1;
                     ()
    | Execute i: let response = contract-call @approver i tz0.00;
                 let _ = ( response.1 ? False: fail | True: ());
                 ( map-get i @map ?
                 | None: fail  # This should not happen
                 | Some line: @map <- map-update i None @map;
                              contract-call line.Destination () line.Amount))

My tz0.02 about this contract:

* my guess is, the approving contract returns the index number because it would
  be too much hassle to give it a storage slot. Having that automated out, we
  could do it. The approver signature would then become `nat->bool`.

* when registering a line, the index number is allocated by the contract, and not
  returned to the caller. I'm not sure how the approver could decide anything
  with so little information, I think this number should be returned as the 
  contract's result.

* the strings in the registered lines don't seem to be used. Shouldn't we refer
  to lines by their name rather than by number? This would imply  to check their
  unicity, and to use them as map keys.

    type t_param = Register: (string * account * tez) + Execute: string

    @approver :: contract nat bool
    @map      :: map string (account * tez)

    \(p :: t_param):
    ( p ?
    | Register line: let id = line.0;
                     let _ = map-mem id @map ? True: fail | False: ();
                     let entry = (line.1, line.2);
                     @map <- map-update @index (Some entry) @map;
                     ()
    | Execute id: let response = contract-call @approver id tz0.00;
                 let _ = ( response.1 ? False: fail | True: ());
                 ( map-get id @map ?
                 | None: fail  # This should not happen
                 | Some x: @map <- map-update i None @map;
                           contract-call x.0 () x.1))
