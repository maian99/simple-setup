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
import qualified Plutus.Contract as Contract
import qualified Plutus.Trace.Emulator as Trace
import qualified PlutusTx
import Prelude
import Wallet.Emulator (knownWallet)

data Test

instance TScripts.ValidatorTypes Test where
  type DatumType Test = ()
  type RedeemerType Test = ()

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

type TestSchema = Contract.Endpoint "Init" () Contract..\/ Contract.Endpoint "Consume" ()

initOutput :: forall w s. Contract.Contract w s Contract.ContractError ()
initOutput = do
  let tx = Constraints.mustPayToTheScript () (Ada.lovelaceValueOf 100)
  void $ Contract.submitTxConstraints testInstance tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId

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

main :: IO ()
main = Trace.runEmulatorTraceIO $ do
  hdl <- Trace.activateContractWallet (knownWallet 1) testEndpoints

  Trace.callEndpoint @"Init" hdl ()
  void $ Trace.waitNSlots 1

  Trace.callEndpoint @"Consume" hdl ()
  void $ Trace.waitNSlots 1
