{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.PSL where
  
import Data.Kind (Type)
import Plutarch.EType
import Plutarch.Core
import GHC.Generics (Generic)
import qualified MonoidDo

data EInteger (f :: ETypeF)
data EValue (f :: ETypeF)
data EUTXO (f :: ETypeF)
data EUTXORef (f :: ETypeF)
data ETokenName (f :: ETypeF)
data ECurrencySymbol (f :: ETypeF)
data ETimeRange (f :: ETypeF)
data EPubKeyHash (f :: ETypeF)

class
  ( Monoid psl
  , EDSL (PSLEDSL psl)
  , IsEType (PSLEDSL psl) EInteger
  ) => PSLDiagram psl datumType | psl -> datumType where
  type PSLEDSL psl :: EType -> Type 
  observeInput :: Term (PSLEDSL psl) EUTXORef -> psl
  causeOwnInput :: Term (PSLEDSL psl) (EOwnUTXO datumType) -> psl
  causeOwnOutput :: Term (PSLEDSL psl) (EOwnUTXO datumType) -> psl
  observeOutput :: Term (PSLEDSL psl) EUTXO -> psl
  causeOutput :: Term (PSLEDSL psl) EUTXO -> psl
  causeOwnMint :: Term (PSLEDSL psl) ETokenName -> PSLEDSL psl EInteger -> psl
  observeMint :: Term (PSLEDSL psl) ECurrencySymbol -> PSLEDSL psl ETokenName -> PSLEDSL psl EInteger -> psl
  requireSignature :: Term (PSLEDSL psl) EPubKeyHash -> psl
  requireValidRange :: Term (PSLEDSL psl) ETimeRange -> psl

data EOwnUTXO d f = EOwnUTXO
  { value :: Ef f EValue
  , datum :: Ef f d
  }

data Protocol where
  Protocol :: forall d (indexType :: EType). (forall psl. PSLDiagram psl d => Term (PSLEDSL psl) indexType -> psl)  -> Protocol

data ENat f = EZ | ES (Ef f ENat)
  deriving stock Generic
  deriving anyclass EIsNewtype

data CounterDatum f = CounterDatum
  { counter :: Ef f ENat
  , pkh :: Ef f EPubKeyHash
  }

data CounterCase f where
  CounterStep :: Ef f ENat -> Ef f EPubKeyHash -> Ef f EValue -> CounterCase f
  CounterConsume :: Ef f EPubKeyHash -> Ef f EValue -> CounterCase f
  deriving stock Generic
  deriving anyclass EIsNewtype


paymentCases :: PSLDiagram psl EPubKeyHash => Term (PSLEDSL psl) EPubKeyHash -> psl
paymentCases pkh = requireSignature pkh

paymentProtocol :: Protocol
paymentProtocol = Protocol paymentCases

counterCases :: PSLDiagram psl CounterDatum => Term (PSLEDSL psl) CounterCase -> psl
counterCases c = ematch c \case
  CounterStep counter pkh value -> MonoidDo.do
    causeOwnInput $ econ $ EOwnUTXO value (econ $ CounterDatum { counter = counter + 1, pkh })
    causeOwnOutput $ econ $ EOwnUTXO value (econ $ CounterDatum { counter, pkh })
  CounterConsume pkh value -> MonoidDo.do
    causeOwnInput $ econ $ EOwnUTXO value (econ $ CounterDatum { counter = 0, pkh })
    requireSignature pkh

counterProtocol :: Protocol
counterProtocol = Protocol counterCases
