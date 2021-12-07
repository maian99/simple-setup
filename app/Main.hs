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

import Control.Monad (void, unless)
import Control.Lens
import qualified Data.Map as M
import Data.Either.Combinators (rightToMaybe)
import Data.Void (Void)
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

data CDPDatum 
  = ManagerDatum 
    { getUsers       :: [Ledger.PubKeyHash]
    , getTotalMinted :: Integer } 
  | UserDatum 
    { getPubKey :: Ledger.PubKeyHash
    , getLocked :: Integer
    , getMinted :: Integer }

data CDP

data CDPActions 
  = Open 
  | Deposit 
  | Withdraw 
  | Mint 
  | Burn

PlutusTx.unstableMakeIsData ''CDPActions
PlutusTx.unstableMakeIsData ''CDPDatum

instance TScripts.ValidatorTypes CDP where
  type DatumType CDP = CDPDatum
  type RedeemerType CDP = CDPActions

{-# INLINEABLE mkValidator #-}
mkValidator :: CDPDatum -> CDPActions -> Ledger.ScriptContext -> Bool
mkValidator _ a _ = case a of 
  Open -> True
  Deposit -> True
  Withdraw -> True
  Mint -> True
  Burn -> True
 
compiledValidator :: TScripts.TypedValidator CDP
compiledValidator = 
  TScripts.mkTypedValidator @CDP
    $$(PlutusTx.compile [||mkValidator||])
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = TScripts.wrapValidator @CDPDatum @CDPActions

validatorScript :: TScripts.Validator
validatorScript = TScripts.validatorScript compiledValidator

validatorAddress :: Ledger.Address
validatorAddress = Ledger.scriptAddress validatorScript

type CDPSchema = Contract.Endpoint "Open" ()
    Contract..\/ Contract.Endpoint "Deposit" Integer
    Contract..\/ Contract.Endpoint "Withdraw" Integer
    Contract..\/ Contract.Endpoint "Mint" Integer
    Contract..\/ Contract.Endpoint "Burn" Integer
    Contract..\/ Contract.Endpoint "Init" ()

getDatum :: PlutusTx.FromData b => Ledger.ChainIndexTxOut -> Maybe b
getDatum o = preview Ledger.ciTxOutDatum o >>= rightToMaybe >>= (PlutusTx.fromBuiltinData . Ledger.getDatum)

getValue :: Ledger.ChainIndexTxOut -> Ledger.Value
getValue = view Ledger.ciTxOutValue

{-# INLINEABLE mkPolicy #-}
mkPolicy :: () -> Ledger.ScriptContext -> Bool
mkPolicy _ _ = True

mintingPolicy :: TScripts.MintingPolicy
mintingPolicy =
  Ledger.mkMintingPolicyScript
    $$(PlutusTx.compile [||TScripts.wrapMintingPolicy mkPolicy||])

mintingPolicyHash :: Scripts.MintingPolicyHash
mintingPolicyHash = Scripts.mintingPolicyHash mintingPolicy

myCurrencySymbol :: Value.CurrencySymbol
myCurrencySymbol = Value.mpsSymbol mintingPolicyHash

myTokenName :: Value.TokenName
myTokenName = "iTSLA"

initOutput :: forall w s. Contract.Contract w s Contract.ContractError ()
initOutput = do
  let lookups = Constraints.typedValidatorLookups compiledValidator
      tx      = Constraints.mustPayToTheScript (ManagerDatum [] 0) (Ada.lovelaceValueOf 1708)
  void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId

openCDP :: Contract.Contract w s Contract.ContractError ()
openCDP = do
  managers <- M.filter containsAuthToken <$> Contract.utxosAt validatorAddress
  myKey <- Contract.ownPubKeyHash 
  let (oref, o) = head $ M.toList managers
      mbUsers = getDatum @CDPDatum o
  case mbUsers of
    Nothing                      -> Contract.throwError "List of users is not available"
    Just (ManagerDatum users tm) -> 
      if myKey `elem` users then Contract.throwError "This user has already openned a CDP"  
      else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
           where lookups = Constraints.typedValidatorLookups compiledValidator
                        <> Constraints.otherScript validatorScript
                        <> Constraints.unspentOutputs (M.fromList [(oref, o)])
                 tx      = Constraints.mustSpendScriptOutput oref (Scripts.Redeemer $ PlutusTx.toBuiltinData Open)
                        <> Constraints.mustPayToTheScript (ManagerDatum (myKey : users) tm) (getValue o)
                        <> Constraints.mustPayToTheScript (UserDatum myKey 0 0) (Ada.lovelaceValueOf 1012)
  where
    containsAuthToken :: Ledger.ChainIndexTxOut -> Bool 
    containsAuthToken o = valid $ getDatum @CDPDatum o
      where valid (Just (ManagerDatum a _)) = True
            valid _                         = False 

depositCDP :: Integer -> Contract.Contract w s Contract.ContractError ()
depositCDP amount = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter containsAuthToken <$> Contract.utxosAt validatorAddress
  myOutputs <- M.filter (containsMyKey myKey) <$> Contract.utxosAt validatorAddress
  let (oref, o) = head $ M.toList managers
      (uoref, uo) = head $ M.toList myOutputs
      mbUsers = getDatum @CDPDatum o
      userDt  = getDatum @CDPDatum uo
  case mbUsers of
    Just (ManagerDatum users tm) -> 
      case userDt of
        Just (UserDatum _ lk mt) ->
          if not $ myKey `elem` users then Contract.throwError "This user has not openned a CDP"
          else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
               where lookups = Constraints.typedValidatorLookups compiledValidator
                            <> Constraints.otherScript validatorScript
                            <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                     tx      = Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData Deposit)
                            <> Constraints.mustPayToTheScript (UserDatum myKey (lk + amount) mt) (getValue uo <> Ada.lovelaceValueOf amount) 
        _ -> Contract.throwError "User's datum is not available"
    _ -> Contract.throwError "List of users is not available"
  where
    containsAuthToken :: Ledger.ChainIndexTxOut -> Bool 
    containsAuthToken o = valid $ getDatum @CDPDatum o
      where valid (Just (ManagerDatum a _)) = True
            valid _                         = False
    containsMyKey :: Ledger.PubKeyHash -> Ledger.ChainIndexTxOut -> Bool
    containsMyKey mk o = valid $ getDatum @CDPDatum o
      where valid (Just (UserDatum k _ _)) = k == mk
            valid _                        = False

withdrawCDP :: Integer -> Contract.Contract w s Contract.ContractError ()
withdrawCDP amount = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter containsAuthToken <$> Contract.utxosAt validatorAddress
  myOutputs <- M.filter (containsMyKey myKey) <$> Contract.utxosAt validatorAddress
  let (oref, o) = head $ M.toList managers
      (uoref, uo) = head $ M.toList myOutputs
      mbUsers = getDatum @CDPDatum o
      userDt  = getDatum @CDPDatum uo
  case mbUsers of
    Just (ManagerDatum users tm) -> 
      case userDt of
        Just (UserDatum _ lk mt) ->
          if not $ myKey `elem` users then Contract.throwError "This user has not openned a CDP"
          else if ((Ada.fromValue $ getValue uo) < Ada.lovelaceOf amount) then Contract.throwError "The withdrawal amount exceeds the locked value" 
               else if (1.3 * ((fromIntegral lk) - (fromIntegral amount)) < 1.5 * 709.6 * (fromIntegral mt)) then Contract.throwError "The withdrawal amount breaks the ratio"
                    else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
                         where lookups = Constraints.typedValidatorLookups compiledValidator
                                      <> Constraints.otherScript validatorScript
                                      <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                               tx      = Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData Withdraw)
                                      <> Constraints.mustPayToTheScript (UserDatum myKey (lk - amount) mt) (getValue uo <> Ada.lovelaceValueOf (-amount)) 
        _ -> Contract.throwError "User's datum is not available"
    _ -> Contract.throwError "List of users is not available"
  where
    containsAuthToken :: Ledger.ChainIndexTxOut -> Bool 
    containsAuthToken o = valid $ getDatum @CDPDatum o
      where valid (Just (ManagerDatum a _)) = True
            valid _                         = False
    containsMyKey :: Ledger.PubKeyHash -> Ledger.ChainIndexTxOut -> Bool
    containsMyKey mk o = valid $ getDatum @CDPDatum o
      where valid (Just (UserDatum k _ _)) = k == mk
            valid _                        = False

mintCDP :: Integer -> Contract.Contract w s Contract.ContractError ()
mintCDP amount = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter containsAuthToken <$> Contract.utxosAt validatorAddress
  myOutputs <- M.filter (containsMyKey myKey) <$> Contract.utxosAt validatorAddress
  let (oref, o) = head $ M.toList managers
      (uoref, uo) = head $ M.toList myOutputs
      mbUsers = getDatum @CDPDatum o
      userDt  = getDatum @CDPDatum uo
  case mbUsers of
    Just (ManagerDatum users tm) -> 
      case userDt of
        Just (UserDatum _ lk mt) ->
          if not $ myKey `elem` users then Contract.throwError "This user has not openned a CDP" 
          else if (1.3* (fromIntegral lk) < 1.5 * 709.67 * ((fromIntegral mt) + (fromIntegral amount))) then Contract.throwError "The minting amount breaks the ratio"
               else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
                    where lookups = Constraints.typedValidatorLookups compiledValidator
                                 <> Constraints.otherScript validatorScript
                                 <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                                 <> Constraints.mintingPolicy mintingPolicy
                          val = Value.assetClassValue (Value.assetClass myCurrencySymbol myTokenName) amount
                          tx      = Constraints.mustMintValue val
                                 <> Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData Mint)
                                 <> Constraints.mustSpendScriptOutput oref (Scripts.Redeemer $ PlutusTx.toBuiltinData Mint)
                                 <> Constraints.mustPayToTheScript (UserDatum myKey lk (mt + amount)) (getValue uo)
                                 <> Constraints.mustPayToTheScript (ManagerDatum (myKey : users) (tm + amount)) (getValue o) 
        _ -> Contract.throwError "User's datum is not available"
    _ -> Contract.throwError "List of users is not available"
  where
    containsAuthToken :: Ledger.ChainIndexTxOut -> Bool 
    containsAuthToken o = valid $ getDatum @CDPDatum o
      where valid (Just (ManagerDatum a _)) = True
            valid _                         = False
    containsMyKey :: Ledger.PubKeyHash -> Ledger.ChainIndexTxOut -> Bool
    containsMyKey mk o = valid $ getDatum @CDPDatum o
      where valid (Just (UserDatum k _ _)) = k == mk
            valid _                        = False

burnCDP :: Integer -> Contract.Contract w s Contract.ContractError ()
burnCDP amount = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter containsAuthToken <$> Contract.utxosAt validatorAddress
  myOutputs <- M.filter (containsMyKey myKey) <$> Contract.utxosAt validatorAddress
  let (oref, o) = head $ M.toList managers
      (uoref, uo) = head $ M.toList myOutputs
      mbUsers = getDatum @CDPDatum o
      userDt  = getDatum @CDPDatum uo
  case mbUsers of
    Just (ManagerDatum users tm) -> 
      case userDt of
        Just (UserDatum _ lk mt) ->
          if not $ myKey `elem` users then Contract.throwError "This user has not openned a CDP" 
          else if (amount > tm) then Contract.throwError "The amount exceeds the current maximal burning size"
               else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
                    where lookups = Constraints.typedValidatorLookups compiledValidator
                                 <> Constraints.otherScript validatorScript
                                 <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                                 <> Constraints.mintingPolicy mintingPolicy
                          val     = Value.assetClassValue (Value.assetClass myCurrencySymbol myTokenName) (-amount)
                          tx      = Constraints.mustMintValue val
                                 <> Constraints.mustSpendScriptOutput oref (Scripts.Redeemer $ PlutusTx.toBuiltinData Mint)
                                 <> Constraints.mustPayToTheScript (ManagerDatum (myKey : users) (tm - amount)) (getValue o) 
        _ -> Contract.throwError "User's datum is not available"
    _ -> Contract.throwError "List of users is not available"
  where
    containsAuthToken :: Ledger.ChainIndexTxOut -> Bool 
    containsAuthToken o = valid $ getDatum @CDPDatum o
      where valid (Just (ManagerDatum a _)) = True
            valid _                         = False
    containsMyKey :: Ledger.PubKeyHash -> Ledger.ChainIndexTxOut -> Bool
    containsMyKey mk o = valid $ getDatum @CDPDatum o
      where valid (Just (UserDatum k _ _)) = k == mk
            valid _                        = False

myEndpoints :: Contract.Contract () CDPSchema Contract.ContractError ()
myEndpoints = Contract.selectList [init, open, deposit, withdraw, mint, burn] >> myEndpoints
  where 
    init = Contract.endpoint @"Init" $ \_ -> Contract.handleError Contract.logError $ initOutput  
    open = Contract.endpoint @"Open" $ \_ -> Contract.handleError Contract.logError openCDP
    deposit = Contract.endpoint @"Deposit" $ \a -> Contract.handleError Contract.logError $ depositCDP a
    withdraw = Contract.endpoint @"Withdraw" $ \a -> Contract.handleError Contract.logError $ withdrawCDP a
    mint = Contract.endpoint @"Mint" $ \a -> Contract.handleError Contract.logError $ mintCDP a
    burn = Contract.endpoint @"Burn" $ \a -> Contract.handleError Contract.logError $ burnCDP a


main :: IO ()
main = Trace.runEmulatorTraceIO $ do
  hdl <- Trace.activateContractWallet (knownWallet 1) myEndpoints
  w2  <- Trace.activateContractWallet (knownWallet 2) myEndpoints

  Trace.callEndpoint @"Init" hdl ()
  void $ Trace.waitNSlots 1

  Trace.callEndpoint @"Open" hdl ()
  void $ Trace.waitNSlots 1
  
  Trace.callEndpoint @"Deposit" hdl 100000
  void $ Trace.waitNSlots 1
  
  Trace.callEndpoint @"Withdraw" hdl 190000
  void $ Trace.waitNSlots 1
