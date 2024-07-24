use aiken/dict
use aiken/hash.{Blake2b_224, Hash}
use aiken/list
use aiken/pairs
use aiken/transaction.{
  InlineDatum, Input, Mint, Output, ScriptContext, Spend, Transaction,
  WithdrawFrom,
}
use aiken/transaction/credential.{
  Inline, Script, ScriptCredential, VerificationKey,
}
use aiken/transaction/value.{PolicyId}

// draft of w0 demo `Maths`

type ScriptHash =
  Hash<Blake2b_224, Script>

type VerificationKeyHash =
  Hash<Blake2b_224, VerificationKey>

type ConfigDatum {
  scripts: List<ScriptHash>,
}

type ConfigAction {
  scripts: List<ScriptHash>,
}

type ConfigMint {
  CMint { scripts: List<ScriptHash> }
  CBurn
}

type MathsDatum {
  value: Int,
  count: Int,
}

type MathsAction {
  maths: Int,
}

type MathsMint {
  MMint { value: Int }
  MBurn
}

type WithdrawAction {
  calcs: List<(Int, Int)>,
}

validator(o: VerificationKeyHash) {
  fn configMint(r: ConfigMint, c: ScriptContext) {
    expect Mint(policy) = c.purpose
    let Transaction { inputs, outputs, mint, extra_signatories, .. } =
      c.transaction

    expect [Pair(tName, tAmt)] =
      mint
        |> value.from_minted_value()
        |> value.tokens(policy)
        |> dict.to_pairs()

    when r is {
      CMint { scripts } -> {
        let configOut =
          list.find(
            outputs,
            fn(output) {
              let outValue =
                output.value
                  |> value.tokens(policy)
                  |> dict.to_pairs()

              outValue == [Pair(tName, tAmt)]
            },
          )
        expect Inline(datum) = configOut.datum
        expect cDatum: ConfigDatum = datum

        list.has(extra_signatories, o) && tAmt == 1 && cDatum.scripts == scripts
      }
      CBurn -> list.has(extra_signatories, o) && tAmt == -1
    }
  }
}

validator(cp: PolicyId) {
  fn configVal(d: ConfigDatum, r: ConfigAction, c: ScriptContext) {
    True
  }
}

validator(cp: PolicyId) {
  fn mathsMint(r: MathsMint, c: ScriptContext) {
    True
  }
}

validator(cp: PolicyId, mp: PolicyId) {
  fn mathsVal(d: MathsDatum, r: MathsAction, c: ScriptContext) {
    let ScriptContext { transaction, .. } = c
    let Transaction { reference_inputs, withdrawals, .. } = transaction

    expect Some(configIn) =
      list.find(
        reference_inputs,
        fn(input) { list.has(value.policies(input.output.value), cp) },
      )

    expect InlineDatum(datum) = configIn.output.datum
    expect cDatum: ConfigDatum = datum

    expect Some(stakeVal) =
      cDatum.scripts
        |> list.at(r.maths)

    pairs.has_key(withdrawals, Inline(ScriptCredential(stakeVal)))
  }
}

validator(cp: PolicyId, mp: PolicyId) {
  fn add(r: WithdrawAction, c: ScriptContext) {
    expect ScriptContext { transaction, purpose: WithdrawFrom(stakeHash) } = c

    let Transaction { inputs, outputs, reference_inputs, .. } = transaction

    mathsIO(
      fn(input, output, mod) {
        expect InlineDatum(datum) = input.datum
        // already input.output
        expect inDatum: MathsDatum = datum

        expect InlineDatum(datum) = output.datum
        expect outDatum: MathsDatum = datum

        inDatum.count + 1 == outDatum.count && inDatum.value + mod == outDatum.value
      },
      r.calcs,
      inputs,
      outputs,
    )
  }
}

validator(cp: PolicyId, mp: PolicyId) {
  fn subtract(r: WithdrawAction, c: ScriptContext) {
    expect ScriptContext { transaction, purpose: WithdrawFrom(stakeHash) } = c

    let Transaction { inputs, outputs, reference_inputs, .. } = transaction

    mathsIO(
      fn(input, output, mod) {
        expect InlineDatum(datum) = input.datum
        // already input.output
        expect inDatum: MathsDatum = datum

        expect InlineDatum(datum) = output.datum
        expect outDatum: MathsDatum = datum

        inDatum.count + 1 == outDatum.count && inDatum.value - mod == outDatum.value
      },
      r.calcs,
      inputs,
      outputs,
    )
  }
}

validator(cp: PolicyId, mp: PolicyId) {
  fn multiply(r: WithdrawAction, c: ScriptContext) {
    expect ScriptContext { transaction, purpose: WithdrawFrom(stakeHash) } = c

    let Transaction { inputs, outputs, reference_inputs, .. } = transaction

    mathsIO(
      fn(input, output, mod) {
        expect InlineDatum(datum) = input.datum
        // already input.output
        expect inDatum: MathsDatum = datum

        expect InlineDatum(datum) = output.datum
        expect outDatum: MathsDatum = datum

        inDatum.count + 1 == outDatum.count && inDatum.value * mod == outDatum.value
      },
      r.calcs,
      inputs,
      outputs,
    )
  }
}

validator(cp: PolicyId, mp: PolicyId) {
  fn divide(r: WithdrawAction, c: ScriptContext) {
    expect ScriptContext { transaction, purpose: WithdrawFrom(stakeHash) } = c

    let Transaction { inputs, outputs, reference_inputs, .. } = transaction

    mathsIO(
      fn(input, output, mod) {
        expect InlineDatum(datum) = input.datum
        // already input.output
        expect inDatum: MathsDatum = datum

        expect InlineDatum(datum) = output.datum
        expect outDatum: MathsDatum = datum

        inDatum.count + 1 == outDatum.count && inDatum.value / mod == outDatum.value
      },
      r.calcs,
      inputs,
      outputs,
    )
  }
}

fn mathsIO(
  validate: fn(Output, Output, Int) -> Bool,
  redeemer: List<(Int, Int)>,
  inputs: List<Input>,
  outputs: List<Output>,
) -> Bool {
  let txList =
    list.map(
      redeemer,
      fn(tuple) {
        let (index, mod) = tuple

        expect Some(output) = list.at(outputs, index)
        expect Some(input) =
          list.find(
            inputs,
            fn(input) {
              value.without_lovelace(input.output.value) == value.without_lovelace(
                output.value,
              )
            },
          )

        (input.output, output, mod)
      },
    )

  list.all(
    txList,
    fn(io) {
      let (input, output, mod) = io

      validate(input, output, mod)
    },
  )
}
