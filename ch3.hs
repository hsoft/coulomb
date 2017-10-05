import Text.Printf
import Geo

ε0 = 8.854 * 10 ** (-12)

densiteSurfacique solide charge = charge / (surface solide)
densiteVolumique solide charge = charge / (volume solide)

chargeSelonDensiteLineique longueur densite = densite * longueur
chargeSelonDensiteSurfacique solide densite = densite * (surface solide)
chargeSelonDensiteVolumique solide densite = densite * (volume solide)

-- args: solide chargé, volume creux?, densité, surface de gauss
champElectrique solide@(Sphere rs) True densite gauss@(Sphere rg)
    | rg < rs = 0
    | otherwise = (chargeSelonDensiteSurfacique solide densite) / (ε0 * (surface gauss))

champElectrique solide@(Sphere rs) False densite gauss@(Sphere rg)
    | rg < rs = 0
    | otherwise = (chargeSelonDensiteVolumique solide densite) / (ε0 * (surface gauss))

champElectrique PlaqueInfinie _ densite _ =
    densite / (2 * ε0)  

densiteSelonLeChamp solide@(Sphere rs) False champ gauss@(Sphere rg) =
    let densite = qin / (volume gauss)
        qin = champ * (surface gauss) * ε0
    in densite

-- EXERCICES

s3 gauss = 
    let s = Sphere 0.3
        d = 6 * 10 ** (-6)
    in  champElectrique s True d gauss

s3a = s3 (Sphere 0.1)
s3b = s3 (Sphere 0.4)
s3c = s3 (Sphere 0.3)

s4 =
    let lt = 0.5
        tige = Cylindre 0 lt
        champ = 7.193 * 10 ** (6) -- N/C
        lg = 0.1
        gauss = Cylindre 0.08 lg
        qin = champ * (surface gauss) * ε0
        densite = qin / lg
        charge = chargeSelonDensiteLineique lt densite
    in charge

s5 =
    let densite = 60 * 10 ** (-6) -- C / m2
        distance = 0.07 -- m
        r = 0.1 -- quelconque
        gauss = Cylindre r distance
    in champElectrique PlaqueInfinie False densite gauss

e31data =
    let rs = 0.1
        solide = (Sphere rs)
    in solide

e31a =
    let solide = e31data
        champ = 2000 -- N/C
        rChamp = 0.05
        gauss = (Sphere rChamp)
    in densiteSelonLeChamp solide False champ gauss

e31b = 
    let solide = e31data
        densite = e31a
        gauss = (Sphere 0.2)
    in champElectrique solide False densite gauss

-- tests

assertEq a b
    | a == b = ()
    | otherwise = error (printf "%s != %s" a b)

scifmt n exp = printf ("%0." ++ (show exp) ++ "e") n

testPairs = [
    (scifmt s3a 2, "0.00e0"),
    (scifmt s3b 2, "3.81e5"),
    (scifmt s3c 2, "6.78e5"),
    (scifmt s4 2, "1.60e-5"),
    (scifmt s5 2, "3.39e6"),
    (scifmt e31a 2, "1.06e-6"),
    (scifmt e31b 2, "1.00e3")]

testAll = map (uncurry assertEq) testPairs
