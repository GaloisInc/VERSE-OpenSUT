# Building Hardened Containers

For the eventual deployment of VERSE tools in DIB, these containers need to be hardened. This is achieved by swapping the open source base image (e.g. `Ubuntu:22.04`  or `redhat/ubi9:9.4` for CN) for an equivalent RedHat image from the [Iron Bank](https://ironbank.dso.mil/about). Because these containers are not publicly accessible (although it is easy to register and get access to the Iron Bank - you just need to in a US based company), they need to be built locally. Below are the steps to do that.

## Regular RedHatUbi9 image

CN is already built for the `redhat/ubi9:9.4` which might be sufficient for your application. If you do not need the hardened image, we recommend downloading the RedHat based image with:

```bash
docker pull ghcr.io/rems-project/cerberus/cn:release-redhat
```

## Fetch the hardened image

First, we need to make sure we are [logged into the Iron Bank](https://docs-ironbank.dso.mil/tutorials/image-pull/), and that we can download the hardened base image:

```bash
docker login -u <username> -p <cli-secret> registry1.dso.mil
docker pull registry1.dso.mil/ironbank/redhat/ubi/ubi9:9.4
```

## Replace the base image

Second, we need to replace the cerberus base ubi9 image with the hardened image. Note that the image checksum seem to be identical for both the open and hardened ubi9 image (see [here](https://hub.docker.com/layers/redhat/ubi9/9.4/images/sha256-970d60bb110b60c175f5b261596957a6c8ccfbd0b252d6a1d28b1655d25cb3a8?context=explore) and [here](https://repo1.dso.mil/dsop/ironbank-pipelines/vat-testing/ubi9/-/commit/c1c778a7c261bb68ec5c318eb2572944c13ac94e)), so the difference it likely minimal, but using the official hardened image simplifies the vetting process. We use `sed`:

```bash
sed -i 's/redhat\/ubi9\:9\.4/registry1\.dso\.mil\/ironbank\/redhat\/ubi\/ubi9\:9\.4/g' src/cerberus/Dockerfile.redhat
# validate by inspecting the file, you should see `FROM registry1.dso.mil...`
head src/cerberus/Dockerfile.redhat
```

## Build with buildx

Finally, we are able to build cerberus image. We recommend using [buildx](https://github.com/docker/buildx) plugin, which can be installed (on Ubuntu-like OSs) with `apt install docker-buildx-plugin`. We eventually want to build the image with [SBOM attestations](https://docs.docker.com/build/metadata/attestations/sbom/) as well as [provenance attestations](https://docs.docker.com/build/metadata/attestations/slsa-provenance/), but that is not possible unless the image is directly pushed into a registry. 

```bash
cd src/cerberus
docker buildx build --tag cn-hardened:1.1 -f Dockerfile.redhat .
```

The build takes around 20-30min. 


## Save and upload the image

Once the image is built, we need to export it and save it, since it should not be pushed into a public registry, and sharing Galois private registry images is complicated.

```bash
docker save cn-hardened:1.1 | gzip > cn-hardened:1.1.tar.gz
```

Upload the resulting image into either Google Drive or your favorite data sharing solution. Note that exporting the same into two different archive files may lead to two different checksum values, which is to be expected. The checksum of the loaded image (see the next step) is the relevant one.


## Load the saved image

To reverse this process and load the image, download `cn-hardened:1.1.tar.gz` first, and then run:

```bash
$ docker load < cn-hardened:1.1.tar.gz
# lets see if the load was successful
$ docker images | grep cn-hardened
cn-hardened                                    1.1                 b50c2f41dda8   6 minutes ago    2.33GB
```
