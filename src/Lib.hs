{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TransformListComp #-}

module Lib
  ( reunion,
    showPeople,
  )
where

import Control.Monad
import Data.Char
import Data.Foldable
import qualified Data.List
import qualified Data.Maybe
import Data.SBV
import Data.SBV.Control
import qualified Data.SBV.List as L
import Data.SBV.Maybe hiding (map)
import Data.Traversable
import qualified Debug.Trace
import Prelude hiding ((!!))

-- | Helper functor
newtype Const a = Const {getConst :: a}

-- | People
data Name
  = SimoneMontleib
  | WolfgangWehrhardt
  | PrincessaTraptenkastel
  | LanceGoldenhope
  | HattieGizmo
  | ProfessorGizmo
  | AlouetteCriminale
  | VinceCriminale
  | GrincellaDisagreeabella
  | FrendleyKindman

nameToString SimoneMontleib = "Simone Montleib"
nameToString WolfgangWehrhardt = "Wolfgang Wehrhardt"
nameToString PrincessaTraptenkastel = "Princessa Traptenkastel"
nameToString LanceGoldenhope = "Lance Goldenhope"
nameToString HattieGizmo = "Hattie Gizmo"
nameToString ProfessorGizmo = "Professor Gizmo"
nameToString AlouetteCriminale = "Alouette Criminale"
nameToString VinceCriminale = "Vince Criminale"
nameToString GrincellaDisagreeabella = "Grincella Disagreeabella"
nameToString FrendleyKindman = "Frendley Kindman"

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
mkSymbolicEnumeration ''Name

data Person f = Person
  { nm :: Name,
    sex :: f Sex,
    roleOne :: f Role,
    roleTwo :: f Role,
    roleThree :: f Role,
    apparentlyDied :: f (Maybe Room),
    isWolfgang :: f (Wolfgang)
  }

names :: [Name]
names =
  [ SimoneMontleib,
    WolfgangWehrhardt,
    PrincessaTraptenkastel,
    LanceGoldenhope,
    HattieGizmo,
    ProfessorGizmo,
    AlouetteCriminale,
    VinceCriminale,
    GrincellaDisagreeabella,
    FrendleyKindman
  ]

liftName :: Name -> SBV Name
liftName SimoneMontleib = sSimoneMontleib
liftName WolfgangWehrhardt = sWolfgangWehrhardt
liftName PrincessaTraptenkastel = sPrincessaTraptenkastel
liftName LanceGoldenhope = sLanceGoldenhope
liftName HattieGizmo = sHattieGizmo
liftName ProfessorGizmo = sProfessorGizmo
liftName AlouetteCriminale = sAlouetteCriminale
liftName VinceCriminale = sVinceCriminale
liftName GrincellaDisagreeabella = sGrincellaDisagreeabella
liftName FrendleyKindman = sFrendleyKindman

newPerson :: Name -> Symbolic (Person SBV)
newPerson n = Person n <$> free_ <*> free_ <*> free_ <*> free_ <*> free_ <*> free_

-- | Get the concrete value of the person in the model
getPerson :: Person SBV -> Query (Person Const)
getPerson Person {nm, sex, roleOne, roleTwo, roleThree, apparentlyDied, isWolfgang} =
  Person nm
    <$> (Const <$> getValue sex)
    <*> (Const <$> getValue roleOne)
    <*> (Const <$> getValue roleTwo)
    <*> (Const <$> getValue roleThree)
    <*> (Const <$> getValue apparentlyDied)
    <*> (Const <$> getValue isWolfgang)

showPeople :: [Person Const] -> [(Name, [Name])] -> [(Name, [Name])] ->  [(Name, [Name])] -> String
showPeople people murders1 murders2 murders3 =
  let (culprits1, culprits2, culprits3, bystanders) = categories
   in Data.List.dropWhileEnd isSpace $
        unlines $
          ["Room 1 Culprits (deaths: " <> deathsInRoom One murders1 <> "):"]
            <> Data.List.sort (fmap nm' culprits1)
            <> ["Room 2 Culprits (deaths: " <> deathsInRoom Two murders2 <> "):"]
            <> Data.List.sort (fmap nm' culprits2)
            <> ["Room 3 Culprits (deaths: " <> deathsInRoom Three murders3 <> "):"]
            <> Data.List.sort (fmap nm' culprits3)
            <> ["Bystanders:"]
            <> Data.List.sort (fmap nm' bystanders)
  where
    nm' = ("  " <>) . (nameToString . nm)
    deathsInRoom room murders = 
      Data.List.intercalate ", " . Data.List.sort $ 
        Data.Maybe.mapMaybe 
          (\(person@Person {nm, apparentlyDied = Const apparentlyDied}) -> 
            if apparentlyDied == (Just room) 
              then Just (unwords ([
                  nameToString nm
                  ] <>
                    if (not (culprit1 person || culprit2 person || culprit3 person))
                    then [
                      "by",
                      "[", 
                      Data.List.intercalate "/" . Data.List.sort . join . Data.Maybe.mapMaybe (\(thisguy, killers) -> if thisguy == nm then Just (map nameToString killers) else Nothing) $ murders,
                      "]"
                      ] else ["(culprit)"]
                )) 
              else Nothing) 
          people
    categories :: ([Person Const], [Person Const], [Person Const], [Person Const])
    categories =
      ( filter culprit1 people,
        filter culprit2 people,
        filter culprit3 people,
        filter (\person -> not (culprit1 person || culprit2 person || culprit3 person)) people
      )

    culprit1 (Person _ _ (Const Culprit) _ _ _ _) = True
    culprit1 _ = False
    culprit2 (Person _ _ _ (Const Culprit) _ _ _) = True
    culprit2 _ = False
    culprit3 (Person _ _ _ _ (Const Culprit) _ _) = True
    culprit3 _ = False

reunion :: IO ([Person Const], [(Name, [Name])], [(Name, [Name])], [(Name, [Name])], String)
reunion = runSMT $ do
  setOption $ ProduceUnsatCores True
  setOption $ OptionKeyword ":smt.core.minimize" ["true"]
  -- Characters
  simone <- person SimoneMontleib sWoman Nothing
  wolfgang <- person WolfgangWehrhardt sMan (Just sOne)
  princessa <- person PrincessaTraptenkastel sWoman (Just sOne)
  lance <- person LanceGoldenhope sMan (Just sOne)
  hattie <- person HattieGizmo sWoman (Just sTwo)
  gizmo <- person ProfessorGizmo sMan (Nothing)
  alouette <- person AlouetteCriminale sWoman (Just sThree)
  vince <- person VinceCriminale sMan (Just sTwo)
  grincella <- person GrincellaDisagreeabella sWoman (Nothing)
  frendley <- person FrendleyKindman sMan (Nothing)

  let people = [simone, wolfgang, princessa, lance, hattie, gizmo, alouette, vince, grincella, frendley]

  let nameToPerson SimoneMontleib = simone
      nameToPerson WolfgangWehrhardt = wolfgang
      nameToPerson PrincessaTraptenkastel = princessa
      nameToPerson LanceGoldenhope = lance
      nameToPerson HattieGizmo = hattie
      nameToPerson ProfessorGizmo = gizmo
      nameToPerson AlouetteCriminale = alouette
      nameToPerson VinceCriminale = vince
      nameToPerson GrincellaDisagreeabella = grincella
      nameToPerson FrendleyKindman = frendley

  couldBeKilledBy <- (newArray "couldBeKilledBy" Nothing) :: Symbolic (SArray Name ([Name]))

  culprits <- sSet "culprits" :: Symbolic (SSet Name)
  murderSets <-  (sSet "murderSets") :: Symbolic (SSet (SArray Int (Maybe Name)))


  {-
  for_ names $ \name -> constrain $ do
    (liftName name) `L.elem` culprits .== culprit (nameToPerson name)

  for_ names $ \name ->
    constrain $
      let p = nameToPerson name
       in (bystander p .&& isJust (apparentlyDied p)) `implies` (L.length ((couldBeKilledBy) `readArray` (liftName name)) .>= 1) --L.length ((couldBeKilledBy) `readArray` (liftName name)) .== ite (bystander p .&& isJust (apparentlyDied p)) 1 0
    -}
  -- Round 1
  murdersRoom1 <- murder One people [wolfgang, lance, princessa] [[gizmo, hattie], [vince, alouette], [grincella, frendley]] couldBeKilledBy alouette lance vince hattie gizmo wolfgang
  inspectBody One hattie wolfgang
  inspectBody One alouette lance
  inspectBody One grincella princessa

  -- Round 2
  murdersRoom2 <- murder Two people [hattie, vince] [[simone, grincella, alouette], [gizmo, frendley]] couldBeKilledBy alouette lance vince hattie gizmo wolfgang
  inspectBody Two gizmo hattie
  inspectBody Two frendley vince
  constrain $ purple gizmo (roleTwo vince .== sBystander)

  -- Round 3
  murdersRoom3 <- murder Three people [alouette] [[simone, frendley], [grincella, gizmo]] couldBeKilledBy alouette lance vince hattie gizmo wolfgang
  inspectBody Three simone alouette

  query $ do
    cs <- checkSat
    case cs of
      Sat -> do
        people <- for people (getPerson)
        couldBeKilledBy <-
          for
            names
            ( \name -> do
                killers <- getValue (couldBeKilledBy `readArray` (liftName name))
                pure (name, killers)
            )
        let murders room =
              fmap Data.Maybe.catMaybes . traverse
                  ( \(name, killers) -> do
                    killers <- for killers $ \(killerName, couldHaveDoneIt) -> do
                      couldBeKiller <- getValue couldHaveDoneIt
                      if couldBeKiller then pure (Just (killerName)) else pure Nothing

                    pure . Just $ (name, Data.Maybe.catMaybes killers)
                  )
        room1Info <- murders One murdersRoom1
        room2Info <- murders Two murdersRoom2
        room3Info <- murders Three murdersRoom1

        observables <- getObservables

        pure (people, room1Info, room2Info, room3Info, Data.List.intercalate "\n" . map show $ observables)
      _ -> do
        unsatCore <- getUnsatCore
        error $ unlines ["Solver said: " <> show cs, "Unsatisfiable constraints:", show unsatCore]
  where
    person name theirSex whenDied = do
      p <- newPerson name
      constrain $ sex p .== theirSex
      constrain $ isWolfgang p .== (if name == WolfgangWehrhardt then sWolfgang else sNotWolfgang)
      constrain $ apparentlyDied p .== (liftMaybe whenDied)
      pure p

    roomToRole One = roleOne
    roomToRole Two = roleTwo
    roomToRole Three = roleThree
    liftRoom One = sOne
    liftRoom Two = sTwo
    liftRoom Three = sThree

    murder room people victims alibiSets couldBeKilledBy alouette lance vince hattie gizmo wolfgang = do
      for_ alibiSets (\alibiSet -> vouch room alibiSet)

      -- Every victim must apparently die in the room they die in
      for_ victims (\victim -> constrain $ apparentlyDied victim .== (liftMaybe $ Just (liftRoom room)))
      for_ (filter (\p -> not (nm p `elem` map nm victims)) people) (\nonvictim -> constrain $ apparentlyDied nonvictim ./= (liftMaybe $ Just (liftRoom room)))

      -- shouldn't be necessary but it's useful for testing
      constrain $ culpritsForRoom .<= (fromIntegral $ length victims)
      {-
      -- And the number of culprits for that room must be greater than or equal to one
      -- and less than or equal to the number of victims who aren't culprits
      constrain $ culpritsForRoom .>= 1

      --And if neither alouette and lance are culprits, there must be at least one man involevd in any
      --murder of a man
      constrain $ purple alouette (purple lance (haveAManToKillAMan))

      -- And if vince is the victim and not a culprit, wolfgang can't have killed him
      when vinceAppearsToBeVictim . constrain $ purple vince (nonWolfgangCulprits .>= 1)
      -}

      -- And every true victim must have exactly one person who could have killed them
      possibleMurders <-
        for
          (pairs people)
          ( \(v, p) ->
              let couldHaveDoneIt = v `computeCouldBeKilledBy` p
               in do
                    constrain $
                      sAnd
                        []
                    -- trueVictim v `implies` ((liftName $ nm p) `L.elem` (couldBeKilledBy `readArray` (liftName $ nm v)) .== couldHaveDoneIt)
                    -- couldHaveDoneIt `implies` (culprit p)

                    pure (v, p, couldHaveDoneIt)
          )     
      
      for_ people $ \p -> do -- make sure all the culprits this round murder at least one person
        let possibileMurderees = map (\(v, _, couldHaveKilled) -> (v, couldHaveKilled)) . filter (\(_, c, _) -> nm c == nm p) $ possibleMurders
        namedConstraint (unwords [nameToString (nm p), "is either victim or kills at least one person in room", show room]) . 
          (\amount -> (((culpritThisRound p) `implies` (amount .>= (1 :: SWord8))))) . sum . map oneIf . map snd $ possibileMurderees
      
      for people $ \p -> do -- make sure all the victims can only be murdered by exactly one person
        let possibileMurderers = map (\(_, c, couldHaveKilled) -> (c, couldHaveKilled)) . filter (\(v, _, _) -> nm v == nm p) $ possibleMurders
        namedConstraint (unwords [nameToString (nm p), "is either culprit or can be killed by exactly one person in room", show room]) . 
          (\amount -> ((observe (unwords [nameToString (nm p), "is a victim in room", show room]) (trueVictim p)) `implies` ((observe (unwords [nameToString (nm p), "could have been killed by this many people in room", show room]) amount) .== (1 :: SWord8)))) . sum . map oneIf . map snd $ possibileMurderers
        pure (nm p, map (\(c, couldHaveKilled) -> (nm c, couldHaveKilled)) possibileMurderers)
      

      where
        computeCouldBeKilledBy v p =
          if nm v == nm p
            then sFalse
            else
                (culprit p .&& trueVictim v) .&&
                ( let c = p
                   in sAnd
                        [ let guarantours = join . Data.Maybe.mapMaybe (\alibiSet -> if (nm c `elem` map nm alibiSet) then Just (filter (\g -> nm g /= nm c) $ alibiSet) else Nothing) $ alibiSets
                           in sAll culprit guarantours,
                          purple alouette (purple lance (sNot (sex v .== sMan .&& sex c .== sWoman))),
                          if nm v == nm vince && nm c == nm wolfgang then sFalse else sTrue,
                          if room == Two && nm c == nm vince && nm v == nm hattie then purple gizmo sFalse else sTrue
                        ]
                )
                
        role = roomToRole room
        trueVictim victim = bystander victim .&& apparentlyDied victim .== (liftMaybe $ Just (liftRoom room))
        culpritThisRound culprit = role culprit .== sCulprit
        trueVictimCountForRoomF f = (sum (map (\victim -> oneIf (bystander victim .&& f victim)) victims)) :: SWord8
        trueVictimsForRoom = trueVictimCountForRoomF $ \_ -> sTrue
        allCulpritsF f = (sum (map (\p -> oneIf $ (culprit p .&& (f p))) people) :: SWord8)
        culpritsForRoomF f = (sum (map (\p -> oneIf $ (culpritThisRound p .&& (f p))) people) :: SWord8)
        culpritsForRoom = culpritsForRoomF $ \_ -> sTrue
        maleCulpritsForRoom = culpritsForRoomF $ \c -> sex c .== sMan
        maleTrueVictimsForRoom = trueVictimCountForRoomF $ \victim -> sex victim .== sMan
        haveAManToKillAMan = ite (maleTrueVictimsForRoom .>= 1) (maleCulpritsForRoom .>= 1) sTrue
        vinceAppearsToBeVictim = Data.List.any (\v -> nm v == nm vince) victims
        nonWolfgangCulprits = culpritsForRoomF $ \c -> isWolfgang c .== sNotWolfgang

    {- s must be true if a bystander says it, otherwise it could be false -}
    purple p s = (bystander p) `implies` s

    {- if the inspector is a bystander, the victim is a bystander (and they better be dead)  -}
    inspectBody room inspector victim = constrain $ purple inspector (bystander victim .&& (apparentlyDied victim .== (liftMaybe $ Just (liftRoom room))))

    pairs l =
      let unmirrored_pairs = [(x, y) | (x : ys) <- Data.List.tails l, y <- ys]
       in unmirrored_pairs <> fmap (\(x, y) -> (y, x)) unmirrored_pairs
    vouch room people = for_ (pairs people) (\(voucher, vouchee) -> constrain $ purple voucher ((roomToRole room) vouchee .== sBystander))

    culprit p = roleOne p .== sCulprit .|| roleTwo p .== sCulprit .|| roleThree p .== sCulprit
    bystander = sNot . culprit

    implies p q = ite p q sTrue
