{-# LANGUAGE DuplicateRecordFields #-}

module Geo (
    Forme(..),
    Solide(..),
    perimetre,
    aire,
    surface,
    volume
) where

data Forme =
    Cercle {rayon :: Float} |
    Rectangle {longueur :: Float, largeur :: Float}
    deriving (Show)

data Solide =
    Sphere {rayon :: Float} |
    Cylindre {rayon :: Float, longueur :: Float}
    deriving (Show)

perimetre (Cercle rayon) = 2 * pi * rayon
perimetre (Rectangle longueur largeur) = 2 * (longueur + largeur)

aire (Cercle rayon) = pi * rayon ^ 2
aire (Rectangle longueur largeur) = longueur * largeur

surface (Sphere rayon) = 4 * pi * rayon ^ 2
surface (Cylindre rayon longueur) = (perimetre (Cercle rayon)) * longueur

volume (Sphere rayon) = (4/3) * pi * rayon ^ 3
