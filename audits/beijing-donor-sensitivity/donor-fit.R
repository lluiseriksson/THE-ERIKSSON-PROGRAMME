args <- commandArgs(trailingOnly=TRUE)
source("factor_functions.R")
source("impute_only.R")
# Preserve first-appearance order in each pivot, including column labels.
as_panel <- function(station, hour, values) {
  codes <- unique(station)
  hours <- unique(hour)
  stopifnot(setequal(hours,1:72), !anyDuplicated(data.frame(station,hour)))
  mat <- matrix(NA_real_,length(codes),length(hours),dimnames=list(codes,as.character(hours)))
  mat[cbind(match(station,codes),match(hour,hours))] <- values
  mat
}
a <- read.csv("data_eps1.csv")
b <- read.csv("data_eps1_extend.csv",check.names=FALSE)
stopifnot(!anyDuplicated(unique(a[c("pollutant_station_code","id_eps")])$pollutant_station_code))
hour <- 1+as.numeric(difftime(as.POSIXct(sprintf("%04d-%02d-%02d %02d:00:00",b$year,b$month,b$day,b$hour),tz="UTC"),
                             as.POSIXct("2016-11-15 00:00:00",tz="UTC"),units="hours"))
pa <- as_panel(a$pollutant_station_code,a$hour_eps,a$pm25)
pb <- as_panel(b$polutant_station_code,hour,b$PM2.5)
stopifnot(all(is.na(pb[13,])))
discarded <- rownames(pb)[13]
pb <- pb[-13,,drop=FALSE]
stopifnot(identical(colnames(pa),as.character(1:72)))
# rbind.data.frame matches columns by name. Impute extended panel in original order.
as_fill <- function(p) {v<-as.matrix(imputed_dat(p));dimnames(v)<-dimnames(p);v}
full <- rbind(as_fill(pa),as_fill(pb)[,colnames(pa)])
raw <- rbind(pa,pb[,colnames(pa)])
restricted <- rbind(as_fill(pa[,1:48]),as_fill(pb[,colnames(pb) %in% as.character(1:48),drop=FALSE])[,as.character(1:48)])
stopifnot(!anyDuplicated(rownames(raw)),all(is.finite(full)),all(is.finite(restricted)))
write.csv(data.frame(station=rownames(raw),raw,check.names=FALSE),"raw.csv",row.names=FALSE,na="")
writeLines(c(paste("excluded",discarded),paste("extended_col_order",paste(colnames(pb),collapse=",")),R.version.string),"fit-info.txt")
for(label in c("full","restricted")) {
 pre <- if(label=="full") full[,1:48] else restricted
 fit <- factor.analysis(scale(t(pre),center=TRUE,scale=FALSE),7,"ml")
 stopifnot(all(is.finite(fit$Gamma)))
 cat(label,fit$niter,fit$converged,"\n",file="fit-info.txt",append=TRUE)
 write.csv(data.frame(station=rownames(raw),apply(fit$Gamma,2,function(x)sprintf("%.12g",x))),paste0(label,"-loadings.csv"),row.names=FALSE,quote=FALSE)
 write.csv(data.frame(station=rownames(raw),pre,check.names=FALSE),paste0(label,"-pre.csv"),row.names=FALSE,quote=FALSE)
}

