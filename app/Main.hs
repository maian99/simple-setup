{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import Control.Monad (void)
import qualified Data.Map as M
import qualified Ledger
import qualified Ledger.Ada as Ada
import qualified Ledger.Constraints as Constraints
import qualified Ledger.Scripts as Scripts
import qualified Ledger.Typed.Scripts as TScripts
import qualified Ledger.Value as Value
import qualified Plutus.Contract as Contract
import qualified Plutus.Trace.Emulator as Trace
import qualified PlutusTx
import Wallet.Emulator (knownWallet)
import Prelude

{-
Test is the data defines the Test output. In this case, DatumType and RedeemerType of all Test outputs are ().
-}
data Test

instance TScripts.ValidatorTypes Test where
  type DatumType Test = ()
  type RedeemerType Test = ()

{-
validateTest is the validation function of Test script. Each time you consume an output from this script,
you have to pass this validation. The function will take 3 arguments:
1. The datum of the output you want to consume, in this case its type is () as non datum.
2. The redeemer contains optional information that you want to push onchain so that you can
easily check, in this case we don't add redeemer so let redeemer be ().
3. The script context includes all information of the transaction.
In this example the validation is always true, which means that you can always consume an utxo.
-}
{-# INLINEABLE validateTest #-}
validateTest :: () -> () -> Ledger.ScriptContext -> Bool
validateTest _ _ _ = True

testInstance :: TScripts.TypedValidator Test
testInstance =
  TScripts.mkTypedValidator @Test
    $$(PlutusTx.compile [||validateTest||])
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = TScripts.wrapValidator @() @()

testValidator :: TScripts.Validator
testValidator = TScripts.validatorScript testInstance

testAddress :: Ledger.Address
testAddress = Ledger.scriptAddress testValidator

{-
mkPolicy is the minting policy function of a token. A token type is represented
by AssetClass, contains 2 fields:
1. Value.CurrencySymbol: actually this is minting policy of the token, be hashed
to PlutusTx.BuiltinByteString (ByteString).
2. Value.TokenName: name of the token.
Anytime you want to mint a token, you have to pass the minting policy which is
included in the currency symbol of the token. As the minting policy is always true,
you can always mint new token.
-}
{-# INLINEABLE mkPolicy #-}
mkPolicy :: () -> Ledger.ScriptContext -> Bool
mkPolicy _ _ = True

mintingPolicy :: TScripts.MintingPolicy
mintingPolicy =
  Ledger.mkMintingPolicyScript
    $$(PlutusTx.compile [||TScripts.wrapMintingPolicy mkPolicy||])

mintingPolicyHash :: Scripts.MintingPolicyHash
mintingPolicyHash = Scripts.mintingPolicyHash mintingPolicy

testCurrencySymbol :: Value.CurrencySymbol
testCurrencySymbol = Value.mpsSymbol mintingPolicyHash

testTokenName :: Value.TokenName
testTokenName = "TEST"

type TestSchema = Contract.Endpoint "Init" () Contract..\/ Contract.Endpoint "Consume" ()

{-
This is the initial endpoint to mint 10 TEST tokens and create an output
at Test script contains all 10 TEST tokens and 100 Ada.
-}
initOutput :: forall w s. Contract.Contract w s Contract.ContractError ()
initOutput = do
  let lookups =
        Constraints.mintingPolicy mintingPolicy
          <> Constraints.typedValidatorLookups testInstance
      val = Value.assetClassValue (Value.assetClass testCurrencySymbol testTokenName) 10
      tx =
        Constraints.mustMintValue val
          <> Constraints.mustPayToTheScript () (Ada.lovelaceValueOf 100 <> val)
  void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId

{-
This endpoint we consume the previous utxo and repay another one contains
50 Ada, which means that you get 50 Ada and 10 TEST tokens to your wallet.
-}
consume :: Contract.Contract w s Contract.ContractError ()
consume = do
  utxos <- M.toList <$> Contract.utxosAt testAddress
  let (oref, o) = head utxos
  let lookups =
        Constraints.typedValidatorLookups testInstance
          <> Constraints.unspentOutputs (M.fromList [(oref, o)])
          <> Constraints.otherScript testValidator
      constraints =
        Constraints.mustSpendScriptOutput oref (Scripts.Redeemer (PlutusTx.toBuiltinData @() ()))
          <> Constraints.mustPayToTheScript () (Ada.lovelaceValueOf 50)
  Contract.submitTxConstraintsWith lookups constraints >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId

testEndpoints :: Contract.Contract () TestSchema Contract.ContractError ()
testEndpoints = Contract.selectList [open, update] >> testEndpoints
  where
    open :: Contract.Promise () TestSchema Contract.ContractError ()
    open = Contract.endpoint @"Init" $ \_ -> Contract.handleError Contract.logError initOutput

    update :: Contract.Promise () TestSchema Contract.ContractError ()
    update = Contract.endpoint @"Consume" $ \_ -> Contract.handleError Contract.logError consume

{-
To test your contract, use EmulatorTrace
-}
main :: IO ()
main = Trace.runEmulatorTraceIO $ do
  -- activate contract from wallet 1. We got function testEndpoints so that we only need to activate all the endpoints once for each wallet.
  hdl <- Trace.activateContractWallet (knownWallet 1) testEndpoints

  -- Endpoint to init output.
  Trace.callEndpoint @"Init" hdl ()
  void $ Trace.waitNSlots 1

  -- Endpoint to consume. This case using the activation from wallet 1 but you can try to activate from another wallet.
  Trace.callEndpoint @"Consume" hdl ()
  void $ Trace.waitNSlots 1
