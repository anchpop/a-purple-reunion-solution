{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Lib
  ( puzzle,
    showPeople,
  )
where

import Data.Char
import Data.Foldable
import Data.List
import Data.Maybe hiding (map)
import Data.SBV
import Data.SBV.Control
import Data.SBV.Maybe hiding (map)
import Data.Traversable
import Control.Monad

-- | Helper functor
newtype Const a = Const {getConst :: a}

-- | Roles
data Role = Culprit | Bystander

-- | Sexes
data Sex = Man | Woman

-- | Rooms
data Room = One | Two | Three

-- | Wolfgang
data Wolfgang = Wolfgang | NotWolfgang

mkSymbolicEnumeration ''Role
mkSymbolicEnumeration ''Sex
mkSymbolicEnumeration ''Room
mkSymbolicEnumeration ''Wolfgang

data Person f = Person
  { nm :: String,
    sex :: f Sex,
    roleOne :: f Role,
    roleTwo :: f Role,
    roleThree :: f Role,
    apparentlyDied :: f (Maybe Room),
    wolfgang :: f (Wolfgang)
  }

data Kill f = Kill {room :: f Room}

newPerson :: String -> Symbolic (Person SBV)
newPerson n = Person n <$> free_ <*> free_ <*> free_ <*> free_ <*> free_ <*> free_

newKill :: Symbolic (Kill SBV)
newKill = Kill <$> free_

-- | Get the concrete value of the person in the model
getPerson :: Person SBV -> Query (Person Const)
getPerson Person {nm, sex, roleOne, roleTwo, roleThree, apparentlyDied, wolfgang} =
  Person nm
    <$> (Const <$> getValue sex)
    <*> (Const <$> getValue roleOne)
    <*> (Const <$> getValue roleTwo)
    <*> (Const <$> getValue roleThree)
    <*> (Const <$> getValue apparentlyDied)
    <*> (Const <$> getValue wolfgang)

showPeople :: [Person Const] -> String
showPeople people =
  let (culprits1, culprits2, culprits3, bystanders) = categories
   in dropWhileEnd isSpace $
        unlines $
          ["Culprits (room 1):"]
            <> fmap nm' culprits1
            <> ["Culprits (room 2):"]
            <> fmap nm' culprits2
            <> ["Culprits (room 3):"]
            <> fmap nm' culprits3
            <> ["Bystanders:"]
            <> fmap nm' bystanders
  where
    nm' = ("  " <>) . nm
    categories :: ([Person Const], [Person Const], [Person Const], [Person Const])
    categories =
      ( filter culprit1 people,
        filter culprit2 people,
        filter culprit3 people,
        filter (\person -> not (culprit1 person || culprit2 person || culprit3 person)) people
      )
      where
        culprit1 (Person n _ (Const Culprit) _ _ _ _) = True
        culprit1 _ = False
        culprit2 (Person n _ _ (Const Culprit) _ _ _) = True
        culprit2 _ = False
        culprit3 (Person n _ _ _ (Const Culprit) _ _) = True
        culprit3 _ = False
    longest = getLongest people
      where
        getLongest :: [Person Const] -> Int
        getLongest = maximum . (fmap length) . (fmap nm)
    padR :: Int -> String -> String
    padR n s
      | length s < n = s ++ replicate (n - length s) ' '
      | otherwise = s

puzzle :: IO ([Person Const])
puzzle = runSMT $ do
  -- Characters
  simone <- person "Simone Montleib" sWoman Nothing
  wolfgang <- person "Wolfgang Wehrhardt" sMan (Just sOne)
  princessa <- person "Princessa Traptenkastel" sWoman (Just sOne)
  lance <- person "Lance Goldenhope" sMan (Just sOne)
  hattie <- person "Hattie Gizmo" sWoman (Just sTwo)
  gizmo <- person "Professor Gizmo" sMan (Nothing)
  alouette <- person "Alouette Criminale" sWoman (Just sThree)
  vince <- person "Vince Criminale" sMan (Just sTwo)
  grincella <- person "Grincella Disagreeabella" sWoman (Nothing)
  frendley <- person "Frendley Kindman" sMan (Nothing)

  let people = [simone, wolfgang, princessa, lance, hattie, gizmo, alouette, vince, grincella, frendley]

  -- Round 1
  murder One people [wolfgang, lance, princessa] alouette lance vince wolfgang
  vouch One [gizmo, hattie]
  vouch One [vince, alouette]
  vouch One [grincella, frendley]
  inspectBody hattie wolfgang
  inspectBody alouette lance
  inspectBody grincella princessa

  -- Round 2
  murder Two people [hattie, vince] alouette lance vince wolfgang
  vouch Two [simone, grincella, alouette]
  vouch Two [gizmo, frendley]
  inspectBody gizmo hattie
  inspectBody frendley vince
  constrain $ purple gizmo (roleTwo vince .== sBystander)

  -- Round 3
  murder Three people [alouette] alouette lance vince wolfgang
  vouch Three [simone, frendley]
  vouch Three [grincella, gizmo]
  inspectBody simone alouette

  query $ do
    cs <- checkSat
    case cs of
      Sat -> do
        people <- for people (getPerson)
        pure people
      _ -> error $ "Solver said: " ++ show cs

  where
    person name theirSex whenDied = do
      person <- newPerson name
      constrain $ sex person .== theirSex
      constrain $ wolfgang person .== (if name == "Wolfgang Wehrhardt" then sWolfgang else sNotWolfgang)
      constrain $ apparentlyDied person .== (liftMaybe whenDied)
      pure person

    roomToRole One = roleOne
    roomToRole Two = roleTwo
    roomToRole Three = roleThree
    liftRoom One = sOne
    liftRoom Two = sTwo
    liftRoom Three = sThree

    {- Every victim must apparently die in the room they die in, and nobody else can die in that room
       And the number of culprits for that room must be greater than one and less than the number of victims who aren't culprits -}
    murder room people victims alouette lance vince wolfgang = do
      for_ victims (\victim -> constrain $ apparentlyDied victim .== (liftMaybe $ Just (liftRoom room)))
      constrain $ culpritsForRoom .>= 1
      constrain $ culpritsForRoom .<= victimsForRoom
      constrain $ purple alouette (purple lance (needAManToKillAMan))
      when vinceAppearsToBeVictim $ constrain $ purple vince (nonWolfgangCulprits .>= 1)
      where
        role = roomToRole room
        victimsForRoomF f = (sum (map (\victim -> oneIf (bystander victim .&& f victim)) victims)) :: SWord8
        victimsForRoom = victimsForRoomF $ \_ -> sTrue
        culpritsForRoomF f = (sum (map (\person -> oneIf $ (role person .== sCulprit .&& (f person))) people) :: SWord8)
        culpritsForRoom = culpritsForRoomF $ \_ -> sTrue
        maleCulpritsForRoom = culpritsForRoomF $ \culprit -> sex culprit .== sMan
        maleVictimsForRoom = victimsForRoomF $ \victim -> sex victim .== sMan
        maleCulprits = (sum (map (\person -> oneIf $ (role person .== sCulprit)) people) :: SWord8)
        needAManToKillAMan = ite (maleVictimsForRoom .>= 1) (maleCulpritsForRoom .>= 1) sTrue
        vinceAppearsToBeVictim = Data.List.any (\victim -> nm victim == nm vince) victims
        nonWolfgangCulprits = culpritsForRoomF $ \culprit -> sex culprit .== sMan
        

    {- s must be true if a bystander says it, otherwise it could be false -}
    purple person s = ite (bystander person) s sTrue

    {- if the inspector is a bystander, the victim is a bystander (and they better be dead)  -}
    inspectBody inspector victim = constrain $ purple inspector (bystander victim)

    pairs l =
      let pairs = [(x, y) | (x : ys) <- tails l, y <- ys]
       in pairs <> fmap (\(x, y) -> (y, x)) pairs
    vouch room people = for_ (pairs people) (\(voucher, vouchee) -> constrain $ purple voucher ((roomToRole room) vouchee .== sBystander))

    culprit person = roleOne person .== sCulprit .|| roleTwo person .== sCulprit .|| roleThree person .== sCulprit
    bystander = sNot . culprit
