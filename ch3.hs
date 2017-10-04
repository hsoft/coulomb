import Geo

ε0 = 8.854 * 10 ** (-12)

densiteSurfacique solide charge = charge / (surface solide)

chargeSelonDensiteSurfacique solide densite = densite * (surface solide)

-- args: solide chargé, volume creux?, charge, surface de gauss
champElectrique solide@(Sphere rs) True charge gauss@(Sphere rg)
    | rg < rs = 0
    | otherwise = charge / (ε0 * (surface gauss))

-- EXERCICES

s3 gauss = 
    let s = Sphere 0.3
        d = 6 * 10 ** (-6)
        c = chargeSelonDensiteSurfacique s d
    in  champElectrique s True c gauss

s3a = s3 (Sphere 0.1)
s3b = s3 (Sphere 0.4)
s3c = s3 (Sphere 0.3)
