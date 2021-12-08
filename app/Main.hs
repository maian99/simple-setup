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
import Control.Lens
import qualified Data.Map as M
import Data.Either.Combinators (rightToMaybe)
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
    { getUsers       :: [Ledger.PubKeyHash] } 
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

containsAuthToken :: Ledger.ChainIndexTxOut -> Bool 
containsAuthToken o = valid $ getDatum @CDPDatum o
  where valid (Just (ManagerDatum _)) = True
        valid _                       = False
        
containsMyKey :: Ledger.PubKeyHash -> Ledger.ChainIndexTxOut -> Bool
containsMyKey mk o = valid $ getDatum @CDPDatum o
  where valid (Just (UserDatum k _ _)) = k == mk
        valid _                        = False

adaPrice :: Double
adaPrice = 1.2

iTSLAPrice :: Double
iTSLAPrice = 709.6

collateralRatio :: Double
collateralRatio = 1.5

maintainRatio :: Integer -> Integer -> Bool
maintainRatio lk mt = adaPrice * (fromIntegral lk) >= collateralRatio * iTSLAPrice * 1000000.0 * (fromIntegral mt)

initOutput :: forall w s. Contract.Contract w s Contract.ContractError ()
initOutput = do
  let lookups = Constraints.typedValidatorLookups compiledValidator
      tx      = Constraints.mustPayToTheScript (ManagerDatum []) (Ada.lovelaceValueOf 1708)
  void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId

openCDP :: Contract.Contract w s Contract.ContractError ()
openCDP = do
  managers <- M.filter containsAuthToken <$> Contract.utxosAt validatorAddress
  myKey <- Contract.ownPubKeyHash 
  let (oref, o) = head $ M.toList managers
      mbUsers = getDatum @CDPDatum o
  case mbUsers of
    Just (ManagerDatum users) -> 
      if myKey `elem` users then Contract.throwError "This user has already openned a CDP"  
      else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
           where lookups = Constraints.typedValidatorLookups compiledValidator
                        <> Constraints.otherScript validatorScript
                        <> Constraints.unspentOutputs (M.fromList [(oref, o)])
                 tx      = Constraints.mustSpendScriptOutput oref (Scripts.Redeemer $ PlutusTx.toBuiltinData Open)
                        <> Constraints.mustPayToTheScript (ManagerDatum (myKey : users)) (getValue o)
                        <> Constraints.mustPayToTheScript (UserDatum myKey 0 0) (Ada.lovelaceValueOf 1012)
    _ -> Contract.throwError "List of users is not available"
                        
depositCDP :: Integer -> Contract.Contract w s Contract.ContractError ()
depositCDP amount = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter containsAuthToken <$> Contract.utxosAt validatorAddress
  myOutputs <- M.filter (containsMyKey myKey) <$> Contract.utxosAt validatorAddress
  if M.null myOutputs then Contract.throwError "This user has not openned a CDP"
   else do 
    let (_, o) = head $ M.toList managers
        (uoref, uo) = head $ M.toList myOutputs
        mbUsers = getDatum @CDPDatum o
        userDt  = getDatum @CDPDatum uo
    case mbUsers of
      Just (ManagerDatum users) -> 
        case userDt of
          Just (UserDatum _ lk mt) ->
            if not $ myKey `elem` users then Contract.throwError "This user has not openned a CDP"
            else if amount < 0 then Contract.throwError "Cannot deposit negative amount"
                 else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
                      where lookups = Constraints.typedValidatorLookups compiledValidator
                                   <> Constraints.otherScript validatorScript
                                   <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                            tx      = Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData Deposit)
                                   <> Constraints.mustPayToTheScript (UserDatum myKey (lk + amount) mt) (getValue uo <> Ada.lovelaceValueOf amount) 
          _ -> Contract.throwError "User's datum is not available"
      _ -> Contract.throwError "List of users is not available"

withdrawCDP :: Integer -> Contract.Contract w s Contract.ContractError ()
withdrawCDP amount = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter containsAuthToken <$> Contract.utxosAt validatorAddress
  myOutputs <- M.filter (containsMyKey myKey) <$> Contract.utxosAt validatorAddress
  if M.null myOutputs then Contract.throwError "This user has not openned a CDP"
   else do
    let (_, o) = head $ M.toList managers
        (uoref, uo) = head $ M.toList myOutputs
        mbUsers = getDatum @CDPDatum o
        userDt  = getDatum @CDPDatum uo
    case mbUsers of
      Just (ManagerDatum users) -> 
        case userDt of
          Just (UserDatum _ lk mt) ->
            if not $ myKey `elem` users then Contract.throwError "This user has not openned a CDP"
            else if amount < 0 then Contract.throwError "Cannot withdraw negative amount"
            else if ((Ada.fromValue $ getValue uo) < Ada.lovelaceOf amount) then Contract.throwError "The withdrawal amount exceeds the locked value" 
                 else if not $ maintainRatio (lk - amount) mt then Contract.throwError "The withdrawal amount breaks the ratio"
                      else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
                           where lookups = Constraints.typedValidatorLookups compiledValidator
                                        <> Constraints.otherScript validatorScript
                                        <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                                 tx      = Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData Withdraw)
                                        <> Constraints.mustPayToTheScript (UserDatum myKey (lk - amount) mt) (getValue uo <> Ada.lovelaceValueOf (-amount)) 
          _ -> Contract.throwError "User's datum is not available"
      _ -> Contract.throwError "List of users is not available"

mintCDP :: Integer -> Contract.Contract w s Contract.ContractError ()
mintCDP amount = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter containsAuthToken <$> Contract.utxosAt validatorAddress
  myOutputs <- M.filter (containsMyKey myKey) <$> Contract.utxosAt validatorAddress
  if M.null myOutputs then Contract.throwError "This user has not openned a CDP"
   else do
    let (_, o) = head $ M.toList managers
        (uoref, uo) = head $ M.toList myOutputs
        mbUsers = getDatum @CDPDatum o
        userDt  = getDatum @CDPDatum uo
    case mbUsers of
      Just (ManagerDatum users) -> 
        case userDt of
          Just (UserDatum _ lk mt) ->
            if not $ myKey `elem` users then Contract.throwError "This user has not openned a CDP" 
            else if amount < 0 then Contract.throwError "Cannot mint negative amount"
            else if not $ maintainRatio lk (mt + amount) then Contract.throwError "The minting amount breaks the ratio"
                 else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
                      where lookups = Constraints.typedValidatorLookups compiledValidator
                                   <> Constraints.otherScript validatorScript
                                   <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                                   <> Constraints.mintingPolicy mintingPolicy
                            val = Value.assetClassValue (Value.assetClass myCurrencySymbol myTokenName) amount
                            tx      = Constraints.mustMintValue val
                                   <> Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData Mint)
                                   <> Constraints.mustPayToTheScript (UserDatum myKey lk (mt + amount)) (getValue uo)
          _ -> Contract.throwError "User's datum is not available"
      _ -> Contract.throwError "List of users is not available"

burnCDP :: Integer -> Contract.Contract w s Contract.ContractError ()
burnCDP amount = do
  myKey <- Contract.ownPubKeyHash
  managers <- M.filter containsAuthToken <$> Contract.utxosAt validatorAddress
  myOutputs <- M.filter (containsMyKey myKey) <$> Contract.utxosAt validatorAddress
  if M.null myOutputs then Contract.throwError "This user has not openned a CDP"
   else do
    let (_, o) = head $ M.toList managers
        (uoref, uo) = head $ M.toList myOutputs
        mbUsers = getDatum @CDPDatum o
        userDt  = getDatum @CDPDatum uo
    case mbUsers of
      Just (ManagerDatum users) -> 
        case userDt of
          Just (UserDatum _ lk mt) ->
            if not $ myKey `elem` users then Contract.throwError "This user has not openned a CDP"
            else if amount < 0 then Contract.throwError "Cannot burn negative amount" 
            else if (amount > mt) then Contract.throwError "The amount exceeds the current maximal burning size"
                 else void $ Contract.submitTxConstraintsWith lookups tx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
                      where lookups = Constraints.typedValidatorLookups compiledValidator
                                   <> Constraints.otherScript validatorScript
                                   <> Constraints.unspentOutputs (M.fromList [(uoref, uo)])
                                   <> Constraints.mintingPolicy mintingPolicy
                            val     = Value.assetClassValue (Value.assetClass myCurrencySymbol myTokenName) (-amount)
                            tx      = Constraints.mustMintValue val
                                   <> Constraints.mustSpendScriptOutput uoref (Scripts.Redeemer $ PlutusTx.toBuiltinData Burn)
                                   <> Constraints.mustPayToTheScript (UserDatum myKey lk (mt - amount)) (getValue uo)
          _ -> Contract.throwError "User's datum is not available"
      _ -> Contract.throwError "List of users is not available"

myEndpoints :: Contract.Contract () CDPSchema Contract.ContractError ()
myEndpoints = Contract.selectList [init', open', deposit', withdraw', mint', burn'] >> myEndpoints
  where 
    init'     = Contract.endpoint @"Init"     $ \_ -> Contract.handleError Contract.logError initOutput  
    open'     = Contract.endpoint @"Open"     $ \_ -> Contract.handleError Contract.logError openCDP
    deposit'  = Contract.endpoint @"Deposit"  $ \a -> Contract.handleError Contract.logError $ depositCDP a
    withdraw' = Contract.endpoint @"Withdraw" $ \a -> Contract.handleError Contract.logError $ withdrawCDP a
    mint'     = Contract.endpoint @"Mint"     $ \a -> Contract.handleError Contract.logError $ mintCDP a
    burn'     = Contract.endpoint @"Burn"     $ \a -> Contract.handleError Contract.logError $ burnCDP a


main :: IO ()
main = Trace.runEmulatorTraceIO $ do
  hdl <- Trace.activateContractWallet (knownWallet 1) myEndpoints

  Trace.callEndpoint @"Init" hdl ()
  void $ Trace.waitNSlots 1

  Trace.callEndpoint @"Open" hdl ()
  void $ Trace.waitNSlots 1
  
  Trace.callEndpoint @"Deposit" hdl 10000000
  void $ Trace.waitNSlots 1
  
  Trace.callEndpoint @"Mint" hdl 1
  void $ Trace.waitNSlots 1
